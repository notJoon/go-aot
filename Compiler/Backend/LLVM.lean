module

public import Compiler.IR
import Compiler.Backend.Symbol
import Std.Data.HashMap

public section

namespace GoAot.Backend.LLVM

private def llvmType (ty : Ty) : String :=
  match ty.kind with
  | .bool => "i1"
  | .float => "double"
  | .signed | .unsigned => "i" ++ toString ty.bits

private def divideMessage : String := "panic: runtime error: integer divide by zero\n"
private def shiftMessage : String := "panic: runtime error: negative shift amount\n"

/-- Runtime declarations and helpers a program uses, collected before any function is emitted. -/
private structure Needs where
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

private def Needs.panics (needs : Needs) : Bool :=
  needs.divide || needs.unsignedDivide || needs.shift

-- Collect declarations and deduplicate string globals before any function is emitted.
private def collectRuntimeNeeds (program : IR.Program) : Needs := Id.run do
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
            let wide := target.floatConversionTy
            let name := s!"llvm.fpto{if wide.isSigned then "s" else "u"}i.sat.{llvmType wide}.f64"
            unless needs.intrinsics.any (·.1 == name) do
              needs := { needs with intrinsics := needs.intrinsics.push (name, wide) }
        | _ => pure ()
  return needs

private def emitBytes (output : String) (bytes : ByteArray) : String := Id.run do
  let mut output := output
  for byte in bytes do
    let value := byte.toNat
    if 32 <= value && value <= 126 && value != 34 && value != 92 then
      output := output.push (Char.ofNat value)
    else
      output := (output.push '\\').push (value / 16).digitChar.toUpper
      output := output.push (value % 16).digitChar.toUpper
  return output

private def hexDigits (value count : Nat) : String :=
  String.ofList ((List.range count).reverse.map fun index => (value / 16 ^ index % 16).digitChar.toUpper)

-- LLVM reads integer constants in the signed range of their width, and doubles as their bits.
private def emitOperand (output : String) (ty : Ty) : IR.Operand → String
  | .value id => output ++ "%v" ++ toString id
  | .literal value =>
    let modulus : Int := (2 ^ ty.bits : Nat)
    let value := value % modulus
    output ++ toString (if value ≥ modulus / 2 then value - modulus else value)
  | .floatLiteral value => output ++ "0x" ++ hexDigits value.toBits.toNat 16
  | .boolLiteral value => output ++ (if value then "true" else "false")
  | .argument index => output ++ "%arg" ++ toString index

private def emitArguments (output : String) (callee : Option IR.Function)
    (arguments : Array IR.Operand) : String := Id.run do
  let types := (callee.map (·.parameters.map (·.ty))).getD #[]
  let mut output := output ++ "("
  for h : index in [:arguments.size] do
    if index != 0 then output := output ++ ", "
    let ty := types[index]?.getD .int
    output := emitOperand (output ++ llvmType ty ++ " ") ty arguments[index]
  return output ++ ")\n"

private def emitBinary (output : String) (id : IR.ValueId) (op : IR.Op) (ty : Ty)
    (left right : IR.Operand) : String :=
  let name := "%v" ++ toString id
  let type := llvmType ty
  if (op == .divide || op == .remainder) && ty.isInteger then
    -- Narrow operands widen to i64, so one helper per signedness covers every width.
    let helper := "@goaot." ++ (if ty.isSigned then "" else "u") ++ (if op == .divide then "div" else "rem")
    if ty.bits == 64 then
      emitOperand (emitOperand (output ++ "  " ++ name ++ " = call i64 " ++ helper ++ "(i64 ") ty left ++
        ", i64 ") ty right ++ ")\n"
    else
      let extend := if ty.isSigned then "sext " else "zext "
      let output := emitOperand (output ++ "  " ++ name ++ ".a = " ++ extend ++ type ++ " ") ty left ++
        " to i64\n"
      let output := emitOperand (output ++ "  " ++ name ++ ".b = " ++ extend ++ type ++ " ") ty right ++
        " to i64\n"
      output ++ "  " ++ name ++ ".wide = call i64 " ++ helper ++ "(i64 " ++ name ++ ".a, i64 " ++
        name ++ ".b)\n  " ++ name ++ " = trunc i64 " ++ name ++ ".wide to " ++ type ++ "\n"
  else
    let operation := match ty.kind, op with
      | .float, .add => "fadd" | .float, .subtract => "fsub" | .float, .multiply => "fmul"
      | .float, .divide => "fdiv" | .float, .remainder => "frem"
      | .float, .equal => "fcmp oeq" | .float, .notEqual => "fcmp une"
      | .float, .less => "fcmp olt" | .float, .lessEqual => "fcmp ole"
      | .float, .greater => "fcmp ogt" | .float, .greaterEqual => "fcmp oge"
      | _, .add => "add" | _, .subtract => "sub" | _, .multiply => "mul"
      | _, .divide => "sdiv" | _, .remainder => "srem"
      | _, .bitAnd => "and" | _, .bitOr => "or" | _, .bitXor => "xor"
      | _, .equal => "icmp eq" | _, .notEqual => "icmp ne"
      | .unsigned, .less => "icmp ult" | .unsigned, .lessEqual => "icmp ule"
      | .unsigned, .greater => "icmp ugt" | .unsigned, .greaterEqual => "icmp uge"
      | _, .less => "icmp slt" | _, .lessEqual => "icmp sle"
      | _, .greater => "icmp sgt" | _, .greaterEqual => "icmp sge"
    emitOperand (emitOperand (output ++ "  " ++ name ++ " = " ++ operation ++ " " ++ type ++ " ") ty left ++
      ", ") ty right ++ "\n"

-- `shl`, `lshr`, and `ashr` are poison for a count at or above the width, so the count is
-- clamped first and the Go result for large counts selected afterwards.
private def emitShift (output : String) (id : IR.ValueId) (op : IR.ShiftOp) (ty : Ty)
    (value : IR.Operand) (countTy : Ty) (count : IR.Operand) : String := Id.run do
  let name := "%v" ++ toString id
  let type := llvmType ty
  let mut output := output
  let mut wide := emitOperand "" countTy count
  if countTy.bits < 64 then
    output := output ++ "  " ++ name ++ ".count = " ++ (if countTy.isSigned then "sext " else "zext ") ++
      llvmType countTy ++ " " ++ wide ++ " to i64\n"
    wide := name ++ ".count"
  if countTy.isSigned then output := output ++ "  call void @goaot.check_shift(i64 " ++ wide ++ ")\n"
  output := output ++ "  " ++ name ++ ".big = icmp uge i64 " ++ wide ++ ", " ++ toString ty.bits ++ "\n"
  output := output ++ "  " ++ name ++ ".clamped = select i1 " ++ name ++ ".big, i64 " ++
    toString (ty.bits - 1) ++ ", i64 " ++ wide ++ "\n"
  let mut amount := name ++ ".clamped"
  if ty.bits < 64 then
    output := output ++ "  " ++ name ++ ".amount = trunc i64 " ++ amount ++ " to " ++ type ++ "\n"
    amount := name ++ ".amount"
  match op, ty.isSigned with
  | .right, true =>
    return emitOperand (output ++ "  " ++ name ++ " = ashr " ++ type ++ " ") ty value ++ ", " ++ amount ++ "\n"
  | _, _ =>
    let operation := if op == .left then "shl" else "lshr"
    output := emitOperand (output ++ "  " ++ name ++ ".raw = " ++ operation ++ " " ++ type ++ " ") ty value ++
      ", " ++ amount ++ "\n"
    return output ++ "  " ++ name ++ " = select i1 " ++ name ++ ".big, " ++ type ++ " 0, " ++ type ++ " " ++
      name ++ ".raw\n"

private def emitConvert (output : String) (id : IR.ValueId) (source target : Ty)
    (value : IR.Operand) : String :=
  let head := output ++ "  %v" ++ toString id ++ " = "
  let sourceType := llvmType source
  let targetType := llvmType target
  match source.kind, target.kind with
  | .float, .signed | .float, .unsigned =>
    let wide := target.floatConversionTy
    let wideType := llvmType wide
    let name := "%v" ++ toString id
    let call := "call " ++ wideType ++ " @llvm.fpto" ++ (if wide.isSigned then "s" else "u") ++ "i.sat." ++
      wideType ++ ".f64(double "
    if wide == target then emitOperand (head ++ call) source value ++ ")\n"
    else
      emitOperand (output ++ "  " ++ name ++ ".wide = " ++ call) source value ++ ")\n  " ++ name ++
        " = trunc " ++ wideType ++ " " ++ name ++ ".wide to " ++ targetType ++ "\n"
  | _, .float =>
    emitOperand (head ++ (if source.isSigned then "sitofp " else "uitofp ") ++ sourceType ++ " ") source value ++
      " to double\n"
  | _, _ =>
    let operation := if source.bits > target.bits then "trunc"
      else if source.bits < target.bits then (if source.isSigned then "sext" else "zext")
      else "bitcast"
    emitOperand (head ++ operation ++ " " ++ sourceType ++ " ") source value ++ " to " ++ targetType ++ "\n"

private def emitPrint (output : String) (temporary : String) (ty : Ty) (value : IR.Operand) : String :=
  match ty.kind with
  | .bool =>
    emitOperand (output ++ "  " ++ temporary ++ " = select i1 ") ty value ++
      ", ptr @.true, ptr @.false\n  call i32 @puts(ptr " ++ temporary ++ ")\n"
  | .float => emitOperand (output ++ "  call void @goaot.print_float(double ") ty value ++ ")\n"
  | kind =>
    let format := if kind == .signed then "@.int_format" else "@.uint_format"
    let (output, wide) := if ty.bits == 64 then (output, emitOperand "" ty value)
      else (emitOperand (output ++ "  " ++ temporary ++ " = " ++ (if kind == .signed then "sext " else "zext ") ++
        llvmType ty ++ " ") ty value ++ " to i64\n", temporary)
    output ++ "  call i32 (ptr, ...) @printf(ptr " ++ format ++ ", i64 " ++ wide ++ ")\n"

private def emitInstructions (functions : Std.HashMap String IR.Function)
    (stringIndices : Std.HashMap ByteArray Nat) (blockIndex : Nat)
    (output : String) (instructions : Array IR.Instruction) : String := Id.run do
  let mut output := output
  for h : index in [:instructions.size] do
    match instructions[index] with
    | .alloca slot ty =>
      output := output ++ s!"  %slot{slot} = alloca {llvmType ty}\n"
    | .load id slot ty =>
      output := output ++ s!"  %v{id} = load {llvmType ty}, ptr %slot{slot}\n"
    | .store slot ty value =>
      output := emitOperand (output ++ s!"  store {llvmType ty} ") ty value ++ s!", ptr %slot{slot}\n"
    | .binary id op ty left right => output := emitBinary output id op ty left right
    | .shift id op ty value countTy count => output := emitShift output id op ty value countTy count
    | .convert id source target value => output := emitConvert output id source target value
    | .call id name arguments =>
      let callee := functions[name]?
      let result := match callee.map (·.returnKind) with
        | some (.value ty) => llvmType ty
        | _ => "i64"
      output := output ++ "  %v" ++ toString id ++ " = call " ++ result ++ " @" ++ Symbol.function name
      output := emitArguments output callee arguments
    | .callVoid name arguments =>
      output := emitArguments (output ++ "  call void @" ++ Symbol.function name) functions[name]? arguments
    | .printString bytes =>
      let index := stringIndices[bytes]!
      output := output ++ "  call void @goaot.print_line(ptr @.str." ++ toString index ++
        ", i64 " ++ toString bytes.size ++ ")\n"
    | .print ty value => output := emitPrint output s!"%print{blockIndex}.{index}" ty value
  return output

private def resultType (function : IR.Function) : String :=
  match function.returnKind with
  | .value ty => llvmType ty
  | .void => if Symbol.isEntry function then "i32" else "void"

private def emitTerminator (function : IR.Function) (output : String) : IR.Terminator → String
  | .br target => output ++ "  br label %bb" ++ toString target ++ "\n"
  | .condBr condition ifTrue ifFalse =>
    emitOperand (output ++ "  br i1 ") .bool condition ++ ", label %bb" ++ toString ifTrue ++
      ", label %bb" ++ toString ifFalse ++ "\n"
  | .ret none =>
    if Symbol.returnsVoid function then output ++ "  ret void\n"
    else output ++ "  ret " ++ resultType function ++ " 0\n"
  | .ret (some value) =>
    let ty := match function.returnKind with | .value ty => ty | .void => .int
    emitOperand (output ++ "  ret " ++ resultType function ++ " ") ty value ++ "\n"

private def emitFunction (functions : Std.HashMap String IR.Function)
    (stringIndices : Std.HashMap ByteArray Nat) (output : String)
    (function : IR.Function) : String := Id.run do
  let linkage := if Symbol.isEntry function then "" else "internal "
  let mut output := output ++ "define " ++ linkage ++ resultType function ++ " @" ++ Symbol.function function.name ++ "("
  for h : index in [:function.parameters.size] do
    if index != 0 then output := output ++ ", "
    output := output ++ llvmType function.parameters[index].ty ++ " %arg" ++ toString index
  output := output ++ ") {\n"
  for h : index in [:function.blocks.size] do
    let block := function.blocks[index]
    if index != 0 then output := output ++ "\n"
    output := output ++ "bb" ++ toString index ++ ":\n"
    output := emitInstructions functions stringIndices index output block.instructions
    output := emitTerminator function output block.terminator
  return output ++ "}\n"

private def lines (text : List String) : String :=
  String.join (text.map (· ++ "\n"))

private def panicMessage (global : String) (message : String) : String :=
  s!"ptr {global}, i64 {message.utf8ByteSize}"

-- Darwin exposes `__stdoutp` so `stdout` is not a portable linkable symbol.
private def printLineHelper : String := lines [
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
private def panicHelper : String := lines [
  "define internal void @goaot.panic(ptr %message, i64 %length) {",
  "  call i32 @fflush(ptr null)",
  "  call i64 @write(i32 2, ptr %message, i64 %length)",
  "  call void @exit(i32 2)",
  "  unreachable", "}"]

-- The most negative value divided by -1 wraps in Go, where `sdiv` and `srem` are undefined.
private def divideHelpers : String :=
  let panic := "  call void @goaot.panic(" ++ panicMessage "@.divide_message" divideMessage ++ ")"
  let helper (name wrap operation : String) := lines [
    s!"define internal i64 @goaot.{name}(i64 %a, i64 %b) \{",
    "entry:", "  %zero = icmp eq i64 %b, 0", "  br i1 %zero, label %panic, label %check", "",
    "panic:", panic, "  unreachable", "",
    "check:", "  %negate = icmp eq i64 %b, -1", "  br i1 %negate, label %wrap, label %divide", "",
    "wrap:"] ++ wrap ++ lines ["", "divide:", s!"  %result = {operation} i64 %a, %b", "  ret i64 %result", "}"]
  helper "div" (lines ["  %negated = sub i64 0, %a", "  ret i64 %negated"]) "sdiv" ++ "\n" ++
    helper "rem" (lines ["  ret i64 0"]) "srem"

private def unsignedDivideHelpers : String :=
  let panic := "  call void @goaot.panic(" ++ panicMessage "@.divide_message" divideMessage ++ ")"
  let helper (name operation : String) := lines [
    s!"define internal i64 @goaot.{name}(i64 %a, i64 %b) \{",
    "entry:", "  %zero = icmp eq i64 %b, 0", "  br i1 %zero, label %panic, label %divide", "",
    "panic:", panic, "  unreachable", "",
    "divide:", s!"  %result = {operation} i64 %a, %b", "  ret i64 %result", "}"]
  helper "udiv" "udiv" ++ "\n" ++ helper "urem" "urem"

private def shiftHelper : String := lines [
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
private def printFloatHelper : String := lines [
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

private def stringGlobal (output name : String) (bytes : ByteArray) : String :=
  emitBytes (output ++ name ++ " = private unnamed_addr constant [" ++ toString (bytes.size + 1) ++
    " x i8] c\"") bytes ++ "\\00\"\n"

def emit (program : IR.Program) : String := Id.run do
  let needs := collectRuntimeNeeds program
  -- Verified IR names every callee, so call sites can take their types from its signature.
  let functions := program.functions.foldl (fun map function => map.insert function.name function) {}
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
  for h : index in [:program.functions.size] do
    if index != 0 then output := output ++ "\n"
    output := emitFunction functions needs.stringIndices output program.functions[index]
  return output

end GoAot.Backend.LLVM
