module

public import Compiler.IR
import Compiler.Backend.Symbol
public import Std.Data.HashMap

/-!
The runtime the LLVM backend links into each program: the constants, libc declarations, and
`goaot.` helpers that its instructions call, emitted only when the program uses them.
-/

public section

namespace GoAot.Backend.LLVM

def llvmType (ty : Ty) : String :=
  match ty.kind with
  | .bool => "i1"
  | .float => "double"
  | .signed | .unsigned => "i" ++ toString ty.bits

def divideMessage : String := "panic: runtime error: integer divide by zero\n"
def shiftMessage : String := "panic: runtime error: negative shift amount\n"

/-- Runtime declarations and helpers a program uses, collected before any function is emitted. -/
structure Needs where
  strings : Array ByteArray := #[]
  stringIndices : Std.HashMap ByteArray Nat := {}
  intFormat : Bool := false
  uintFormat : Bool := false
  bool : Bool := false
  float : Bool := false
  divide : Bool := false
  unsignedDivide : Bool := false
  shift : Bool := false
  /-- Saturating float to integer intrinsics, such as `llvm.fptosi.sat.i8.f64`. -/
  intrinsics : Array (String × Ty) := #[]

def Needs.panics (needs : Needs) : Bool :=
  needs.divide || needs.unsignedDivide || needs.shift

-- Collect declarations and deduplicate string globals before any function is emitted.
def collectRuntimeNeeds (program : IR.Program) : Needs := Id.run do
  let mut needs : Needs := {}
  for function in program.functions do
    for block in function.blocks do
      for instruction in block.instructions do
        match instruction with
        | .printString bytes =>
          unless needs.stringIndices.contains bytes do
            needs := { needs with
              stringIndices := needs.stringIndices.insert bytes needs.strings.size
              strings := needs.strings.push bytes }
        | .print ty _ =>
          match ty.kind with
          | .signed => needs := { needs with intFormat := true }
          | .unsigned => needs := { needs with uintFormat := true }
          | .bool => needs := { needs with bool := true }
          | .float => needs := { needs with float := true }
        | .binary _ op ty .. =>
          if (op == .divide || op == .remainder) && ty.isInteger then
            needs := if ty.isSigned then { needs with divide := true }
              else { needs with unsignedDivide := true }
        | .shift _ _ _ _ countTy _ => if countTy.isSigned then needs := { needs with shift := true }
        | .convert _ source target _ =>
          if source.kind == .float && target.isInteger then
            let wide := IR.floatConversionTy target
            let name := s!"llvm.fpto{if wide.isSigned then "s" else "u"}i.sat.{llvmType wide}.f64"
            unless needs.intrinsics.any (·.1 == name) do
              needs := { needs with intrinsics := needs.intrinsics.push (name, wide) }
        | _ => pure ()
  return needs

def lines (text : List String) : String :=
  String.join (text.map (· ++ "\n"))

def panicMessage (global : String) (message : String) : String :=
  s!"ptr {global}, i64 {message.utf8ByteSize}"

-- Darwin exposes `__stdoutp` so `stdout` is not a portable linkable symbol.
def printLineHelper : String := lines [
  "define internal void @goaot.print_line(ptr %bytes, i64 %length) {",
  "entry:", "  %newline = alloca i8", "  store i8 10, ptr %newline",
  "  call i32 @fflush(ptr null)", "  br label %loop", "", "loop:",
  "  %offset = phi i64 [ 0, %entry ], [ %next, %body ]",
  "  %done = icmp eq i64 %offset, %length",
  "  br i1 %done, label %exit, label %body", "", "body:",
  "  %address = getelementptr i8, ptr %bytes, i64 %offset",
  "  %remaining = sub i64 %length, %offset",
  "  %written = call i64 @write(i32 1, ptr %address, i64 %remaining)",
  "  %next = add i64 %offset, %written", "  %failed = icmp slt i64 %written, 1",
  "  br i1 %failed, label %exit, label %loop", "",
  "exit:", "  call i64 @write(i32 1, ptr %newline, i64 1)", "  ret void", "}"]

-- Go panics with exit status 2 after flushing what the program already printed.
def panicHelper : String := lines [
  "define internal void @goaot.panic(ptr %message, i64 %length) {",
  "  call i32 @fflush(ptr null)",
  "  call i64 @write(i32 2, ptr %message, i64 %length)",
  "  call void @exit(i32 2)",
  "  unreachable", "}"]

-- The most negative value divided by -1 wraps in Go, where `sdiv` and `srem` are undefined.
def divideHelpers : String :=
  let panic := "  call void @goaot.panic(" ++ panicMessage "@.divide_message" divideMessage ++ ")"
  let helper (name wrap operation : String) := lines [
    s!"define internal i64 @goaot.{name}(i64 %a, i64 %b) \{",
    "entry:", "  %zero = icmp eq i64 %b, 0", "  br i1 %zero, label %panic, label %check", "",
    "panic:", panic, "  unreachable", "",
    "check:", "  %negate = icmp eq i64 %b, -1", "  br i1 %negate, label %wrap, label %divide", "",
    "wrap:"] ++ wrap ++ lines ["", "divide:", s!"  %result = {operation} i64 %a, %b", "  ret i64 %result", "}"]
  helper "div" (lines ["  %negated = sub i64 0, %a", "  ret i64 %negated"]) "sdiv" ++ "\n" ++
    helper "rem" (lines ["  ret i64 0"]) "srem"

def unsignedDivideHelpers : String :=
  let panic := "  call void @goaot.panic(" ++ panicMessage "@.divide_message" divideMessage ++ ")"
  let helper (name operation : String) := lines [
    s!"define internal i64 @goaot.{name}(i64 %a, i64 %b) \{",
    "entry:", "  %zero = icmp eq i64 %b, 0", "  br i1 %zero, label %panic, label %divide", "",
    "panic:", panic, "  unreachable", "",
    "divide:", s!"  %result = {operation} i64 %a, %b", "  ret i64 %result", "}"]
  helper "udiv" "udiv" ++ "\n" ++ helper "urem" "urem"

def shiftHelper : String := lines [
  "define internal void @goaot.check_shift(i64 %count) {",
  "entry:", "  %negative = icmp slt i64 %count, 0",
  "  br i1 %negative, label %panic, label %done", "",
  "panic:", "  call void @goaot.panic(" ++ panicMessage "@.shift_message" shiftMessage ++ ")",
  "  unreachable", "", "done:", "  ret void", "}"]

/-
Go prints a float64 as `strconv.FormatFloat(v, 'g', -1, 64)`: the shortest digits that round trip,
in `%e` form when the exponent is below -4 or at least 6. The shortest precision whose `%e` output
parses back to `v` gives those digits, and C's `%e` and `%f` then produce Go's layout.
-/
def printFloatHelper : String := lines [
  "define internal void @goaot.print_float(double %value) {",
  "entry:", "  %buffer = alloca [32 x i8]", "  %nan = fcmp uno double %value, %value",
  "  br i1 %nan, label %print_nan, label %check_infinity", "",
  "print_nan:", "  call i32 @puts(ptr @.nan)", "  ret void", "",
  "check_infinity:", "  %magnitude = call double @llvm.fabs.f64(double %value)",
  "  %infinite = fcmp oeq double %magnitude, 0x7FF0000000000000",
  "  br i1 %infinite, label %print_infinity, label %search", "",
  "print_infinity:", "  %positive = fcmp ogt double %value, 0.0",
  "  %text = select i1 %positive, ptr @.plus_infinity, ptr @.minus_infinity",
  "  call i32 @puts(ptr %text)", "  ret void", "",
  "search:", "  br label %loop", "",
  "loop:", "  %precision = phi i32 [ 0, %search ], [ %next, %retry ]",
  "  call i32 (ptr, i64, ptr, ...) @snprintf(ptr %buffer, i64 32, ptr @.float_digits, i32 %precision, double %value)",
  "  %parsed = call double @strtod(ptr %buffer, ptr null)",
  "  %exact = fcmp oeq double %parsed, %value", "  %last = icmp eq i32 %precision, 16",
  "  %done = or i1 %exact, %last", "  br i1 %done, label %format, label %retry", "",
  "retry:", "  %next = add i32 %precision, 1", "  br label %loop", "",
  "format:", "  %marker = call ptr @strchr(ptr %buffer, i32 101)",
  "  %exponent.text = getelementptr i8, ptr %marker, i64 1",
  "  %exponent = call i64 @strtol(ptr %exponent.text, ptr null, i32 10)",
  "  %small = icmp slt i64 %exponent, -4", "  %large = icmp sge i64 %exponent, 6",
  "  %scientific = or i1 %small, %large",
  "  br i1 %scientific, label %print_scientific, label %print_fixed", "",
  "print_scientific:",
  "  call i32 (ptr, ...) @printf(ptr @.float_scientific, i32 %precision, double %value)",
  "  ret void", "",
  "print_fixed:", "  %precision.wide = sext i32 %precision to i64",
  "  %fraction = sub i64 %precision.wide, %exponent", "  %whole = icmp slt i64 %fraction, 0",
  "  %fraction.clamped = select i1 %whole, i64 0, i64 %fraction",
  "  %fraction.narrow = trunc i64 %fraction.clamped to i32",
  "  call i32 (ptr, ...) @printf(ptr @.float_fixed, i32 %fraction.narrow, double %value)",
  "  ret void", "}"]

def stringGlobal (output name : String) (bytes : ByteArray) : String :=
  Symbol.escape (output ++ name ++ " = private unnamed_addr constant [" ++ toString (bytes.size + 1) ++
    " x i8] c\"") bytes ++ "\\00\"\n"

/-- The globals, declarations, and helpers `needs` asks for, which precede the program's functions. -/
def runtime (needs : Needs) : String := Id.run do
  let needsWrite := !needs.strings.isEmpty || needs.panics
  let needsPrintf := needs.intFormat || needs.uintFormat || needs.float
  let needsPuts := needs.bool || needs.float

  let mut output := ""
  for h : i in [:needs.strings.size] do
    output := stringGlobal output ("@.str." ++ toString i) needs.strings[i]
  if needs.intFormat then
    output := output ++ "@.int_format = private unnamed_addr constant [6 x i8] c\"%lld\\0A\\00\"\n"
  if needs.uintFormat then
    output := output ++ "@.uint_format = private unnamed_addr constant [6 x i8] c\"%llu\\0A\\00\"\n"
  if needs.bool then
    output := stringGlobal (stringGlobal output "@.true" "true".toUTF8) "@.false" "false".toUTF8
  if needs.float then
    output := stringGlobal (stringGlobal (stringGlobal output "@.nan" "NaN".toUTF8)
      "@.plus_infinity" "+Inf".toUTF8) "@.minus_infinity" "-Inf".toUTF8
    output := stringGlobal (stringGlobal (stringGlobal output "@.float_digits" "%.*e".toUTF8)
      "@.float_scientific" "%.*e\n".toUTF8) "@.float_fixed" "%.*f\n".toUTF8
  if needs.divide || needs.unsignedDivide then
    output := stringGlobal output "@.divide_message" divideMessage.toUTF8
  if needs.shift then output := stringGlobal output "@.shift_message" shiftMessage.toUTF8
  if output != "" then output := output ++ "\n"

  let mut declarations := ""
  if needsWrite then declarations := declarations ++ "declare i32 @fflush(ptr)\ndeclare i64 @write(i32, ptr, i64)\n"
  if needsPrintf then declarations := declarations ++ "declare i32 @printf(ptr, ...)\n"
  if needsPuts then declarations := declarations ++ "declare i32 @puts(ptr)\n"
  if needs.panics then declarations := declarations ++ "declare void @exit(i32)\n"
  if needs.float then declarations := declarations ++
    "declare i32 @snprintf(ptr, i64, ptr, ...)\ndeclare double @strtod(ptr, ptr)\n" ++
    "declare ptr @strchr(ptr, i32)\ndeclare i64 @strtol(ptr, ptr, i32)\n" ++
    "declare double @llvm.fabs.f64(double)\n"
  for (name, target) in needs.intrinsics do
    declarations := declarations ++ "declare " ++ llvmType target ++ " @" ++ name ++ "(double)\n"
  if declarations != "" then output := output ++ declarations ++ "\n"

  for (needed, helper) in [(!needs.strings.isEmpty, printLineHelper), (needs.panics, panicHelper),
      (needs.divide, divideHelpers), (needs.unsignedDivide, unsignedDivideHelpers),
      (needs.shift, shiftHelper), (needs.float, printFloatHelper)] do
    if needed then output := output ++ helper ++ "\n"
  return output

end GoAot.Backend.LLVM
