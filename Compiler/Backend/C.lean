module

public import Compiler.IR
import Compiler.Backend.Symbol
import Std.Data.HashMap
import Std.Data.HashSet

public section

namespace GoAot.Backend.C

/-- Bools are `int64_t` holding 0 or 1, which is what a C comparison produces. -/
private def cType : Ty → String
  | .bool | .int | .int64 => "int64_t"
  | .int8 => "int8_t" | .int16 => "int16_t" | .int32 => "int32_t"
  | .uint | .uint64 => "uint64_t"
  | .uint8 => "uint8_t" | .uint16 => "uint16_t" | .uint32 => "uint32_t"
  | .float64 => "double"

private def hexDigits (value count : Nat) : String :=
  String.ofList ((List.range count).reverse.map fun index => (value / 16 ^ index % 16).digitChar)

/-- An exact C99 hexadecimal literal for a finite float64. -/
private def floatLiteral (value : Float) : String :=
  let bits := value.toBits.toNat
  let sign := if bits / 2 ^ 63 == 1 then "-" else ""
  let exponent : Nat := bits / 2 ^ 52 % 2048
  let fraction := hexDigits (bits % 2 ^ 52) 13
  if exponent == 0 then sign ++ "0x0." ++ fraction ++ "p-1022"
  else sign ++ "0x1." ++ fraction ++ "p" ++ toString ((exponent : Int) - 1023)

-- The most negative int64 has no C literal, and literals above it need an unsigned suffix.
private def intLiteral (value : Int) : String :=
  if value == Ty.int64.minValue then "(-9223372036854775807 - 1)"
  else if value > Ty.int64.maxValue then toString value ++ "u"
  else if value < 0 then "(" ++ toString value ++ ")"
  else toString value

private def emitParameters (output : String) (parameters : Array IR.Parameter) : String := Id.run do
  if parameters.isEmpty then return output ++ "void"
  let mut output := output
  for h : index in [:parameters.size] do
    if index != 0 then output := output ++ ", "
    output := output ++ cType parameters[index].ty ++ " arg_" ++ parameters[index].name
  return output

private def emitOperand (parameters : Array IR.Parameter) (output : String) : IR.Operand → String
  | .value id => output ++ "tmp_" ++ toString id
  | .literal value => output ++ intLiteral value
  | .floatLiteral value => output ++ floatLiteral value
  | .boolLiteral value => output ++ (if value then "1" else "0")
  | .argument index => output ++ "arg_" ++ ((parameters[index]?.map (·.name)).getD "")

-- Fixed width escapes stop C from consuming following hexadecimal characters.
private def emitBytes (output : String) (bytes : ByteArray) : String := Id.run do
  let mut output := output
  for byte in bytes do
    let value := byte.toNat
    output := (output ++ "\\x").push (value / 16).digitChar.toUpper
    output := output.push (value % 16).digitChar.toUpper
  return output

-- Values are used only in their defining block, so a block's operands decide which call
-- results need a C variable. Discarded results would otherwise trigger -Wunused-variable.
private def usedValues (block : IR.Block) : Std.HashSet IR.ValueId := Id.run do
  let mut used := {}
  let add (used : Std.HashSet IR.ValueId) : IR.Operand → Std.HashSet IR.ValueId
    | .value id => used.insert id
    | _ => used
  for instruction in block.instructions do
    used := match instruction with
      | .store _ _ value | .print _ value | .convert _ _ _ value => add used value
      | .binary _ _ _ left right | .shift _ _ _ left _ right => add (add used left) right
      | .call _ _ arguments | .callVoid _ arguments => arguments.foldl add used
      | .alloca .. | .load .. | .printString _ => used
  return match block.terminator with
    | .condBr condition .. => add used condition
    | .ret (some value) => add used value
    | .br _ | .ret none => used

private def emitArguments (parameters : Array IR.Parameter) (output : String)
    (arguments : Array IR.Operand) : String := Id.run do
  let mut output := output ++ "("
  for h : index in [:arguments.size] do
    if index != 0 then output := output ++ ", "
    output := emitOperand parameters output arguments[index]
  return output ++ ");\n"

/-
Integer `+`, `-`, `*`, and bitwise operators run on `uint64_t` and convert back, because C
leaves signed overflow undefined and promotes narrow unsigned operands to a signed `int`.
Converting an out of range value to a signed type wraps in every compiler the tests use.
-/
private def emitBinary (parameters : Array IR.Parameter) (output : String) (op : IR.Op)
    (ty : Ty) (left right : IR.Operand) : String :=
  let operand := emitOperand parameters
  let symbol := match op with
    | .add => "+" | .subtract => "-" | .multiply => "*" | .divide => "/" | .remainder => "%"
    | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
    | .equal => "==" | .notEqual => "!=" | .less => "<" | .lessEqual => "<="
    | .greater => ">" | .greaterEqual => ">="
  if op.isComparison || ty.kind == .float then
    operand (operand output left ++ " " ++ symbol ++ " ") right
  else if op == .divide || op == .remainder then
    let helper := (if ty.isSigned then "goaot_" else "goaot_u") ++ (if op == .divide then "div" else "rem")
    operand (operand (output ++ "(" ++ cType ty ++ ")" ++ helper ++ "(") left ++ ", ") right ++ ")"
  else
    operand (operand (output ++ "(" ++ cType ty ++ ")((uint64_t)") left ++ " " ++ symbol ++ " (uint64_t)")
      right ++ ")"

private def emitShift (parameters : Array IR.Parameter) (output : String) (op : IR.ShiftOp)
    (ty : Ty) (value : IR.Operand) (count : IR.Operand) : String :=
  let operand := emitOperand parameters
  let count := operand "(uint64_t)" count
  let bits := toString ty.bits
  let output := output ++ "(" ++ cType ty ++ ")("
  match op, ty.isSigned with
  | .right, true =>
    operand (output ++ "(int64_t)") value ++ " >> (" ++ count ++ " >= " ++ bits ++ " ? " ++
      toString (ty.bits - 1) ++ " : " ++ count ++ "))"
  | _, _ =>
    operand (output ++ count ++ " >= " ++ bits ++ " ? 0 : (uint64_t)") value ++
      (if op == .left then " << " else " >> ") ++ count ++ ")"

private def emitConvert (parameters : Array IR.Parameter) (output : String) (source target : Ty)
    (value : IR.Operand) : String :=
  let output := output ++ "(" ++ cType target ++ ")"
  if source.kind == .float && target.isInteger then
    let wide := target.floatConversionTy
    if wide.isSigned then
      emitOperand parameters (output ++ "goaot_f64_to_int(") value ++ ", " ++
        intLiteral wide.minValue ++ ", " ++ intLiteral wide.maxValue ++ ")"
    else
      emitOperand parameters (output ++ "goaot_f64_to_uint(") value ++ ", " ++
        intLiteral wide.maxValue ++ ")"
  else emitOperand parameters output value

private def resultType (functions : Std.HashMap String IR.Function) (name : String) : Ty :=
  match functions[name]? with
  | some { returnKind := .value ty, .. } => ty
  | _ => .int

-- Explicit byte counts preserve embedded NUL values during string output.
private def emitInstructions (functions : Std.HashMap String IR.Function)
    (parameters : Array IR.Parameter) (output : String) (block : IR.Block) : String := Id.run do
  let used := usedValues block
  let operand := emitOperand parameters
  let mut output := output
  for instruction in block.instructions do
    match instruction with
    | .alloca .. => pure () -- Slot declarations are emitted outside the block braces.
    | .load id slot ty =>
      output := output ++ s!"    {cType ty} tmp_{id} = slot_{slot};\n"
    | .store slot _ value =>
      output := operand (output ++ s!"    slot_{slot} = ") value ++ ";\n"
    | .binary id op ty left right =>
      let resultTy := if op.isComparison then Ty.bool else ty
      output := emitBinary parameters (output ++ s!"    {cType resultTy} tmp_{id} = ") op ty left right ++
        ";\n"
    | .shift id op ty value countTy count =>
      if countTy.isSigned then output := operand (output ++ "    goaot_check_shift(") count ++ ");\n"
      output := emitShift parameters (output ++ s!"    {cType ty} tmp_{id} = ") op ty value count ++
        ";\n"
    | .convert id source target value =>
      output := emitConvert parameters (output ++ s!"    {cType target} tmp_{id} = ") source target
        value ++ ";\n"
    | .call id name arguments =>
      output := output ++ "    "
      if used.contains id then
        output := output ++ cType (resultType functions name) ++ " tmp_" ++ toString id ++ " = "
      output := emitArguments parameters (output ++ Symbol.function name) arguments
    | .callVoid name arguments =>
      output := emitArguments parameters (output ++ "    " ++ Symbol.function name) arguments
    | .printString bytes =>
      output := emitBytes (output ++ "    fwrite(\"") bytes ++
        "\", 1, " ++ toString bytes.size ++ ", stdout); putchar('\\n');\n"
    | .print ty value =>
      output := match ty.kind with
        | .signed => operand (output ++ "    printf(\"%lld\\n\", (long long)") value ++ ");\n"
        | .unsigned =>
          operand (output ++ "    printf(\"%llu\\n\", (unsigned long long)") value ++ ");\n"
        | .bool => operand (output ++ "    puts(") value ++ " ? \"true\" : \"false\");\n"
        | .float => operand (output ++ "    goaot_print_float(") value ++ ");\n"
  return output

private def emitTerminator (function : IR.Function) (output : String) : IR.Terminator → String
  | .br target => output ++ "    goto bb" ++ toString target ++ ";\n"
  | .condBr condition ifTrue ifFalse =>
    emitOperand function.parameters (output ++ "    if (") condition ++ ") goto bb" ++
      toString ifTrue ++ "; else goto bb" ++ toString ifFalse ++ ";\n"
  | .ret none =>
    output ++ (if Symbol.returnsVoid function then "    return;\n" else "    return 0;\n")
  | .ret (some value) => emitOperand function.parameters (output ++ "    return ") value ++ ";\n"

private def emitHeader (output : String) (function : IR.Function) : String :=
  let result := match function.returnKind with
    | .value ty => cType ty
    | .void => if Symbol.isEntry function then "int" else "void"
  emitParameters (output ++ result ++ " " ++ Symbol.function function.name ++ "(") function.parameters ++ ")"

private def lines (text : List String) : String :=
  String.intercalate "\n" text

private def panicHelper : String := lines [
  "static void goaot_panic(const char *message) {",
  "  fflush(stdout);",
  "  fputs(message, stderr);",
  "  exit(2);",
  "}"]

-- C leaves the most negative value divided by -1 undefined, while Go wraps it.
private def divideHelpers : String := lines [
  "static int64_t goaot_div(int64_t a, int64_t b) {",
  "  if (b == 0) goaot_panic(\"panic: runtime error: integer divide by zero\\n\");",
  "  return b == -1 ? (int64_t)(0 - (uint64_t)a) : a / b;",
  "}",
  "",
  "static int64_t goaot_rem(int64_t a, int64_t b) {",
  "  if (b == 0) goaot_panic(\"panic: runtime error: integer divide by zero\\n\");",
  "  return b == -1 ? 0 : a % b;",
  "}"]

private def unsignedDivideHelpers : String := lines [
  "static uint64_t goaot_udiv(uint64_t a, uint64_t b) {",
  "  if (b == 0) goaot_panic(\"panic: runtime error: integer divide by zero\\n\");",
  "  return a / b;",
  "}",
  "",
  "static uint64_t goaot_urem(uint64_t a, uint64_t b) {",
  "  if (b == 0) goaot_panic(\"panic: runtime error: integer divide by zero\\n\");",
  "  return a % b;",
  "}"]

private def shiftHelper : String := lines [
  "static void goaot_check_shift(int64_t count) {",
  "  if (count < 0) goaot_panic(\"panic: runtime error: negative shift amount\\n\");",
  "}"]

-- Out of range conversions saturate and NaN becomes 0, like LLVM's `fptosi.sat`.
private def floatToIntHelpers : String := lines [
  "static int64_t goaot_f64_to_int(double x, int64_t low, int64_t high) {",
  "  if (x != x) return 0;",
  "  if (x <= (double)low) return low;",
  "  if (x >= (double)high + 1.0) return high;",
  "  return (int64_t)x;",
  "}",
  "",
  "static uint64_t goaot_f64_to_uint(double x, uint64_t high) {",
  "  if (x != x || x <= 0) return 0;",
  "  if (x >= (double)high + 1.0) return high;",
  "  return (uint64_t)x;",
  "}"]

/-
Go prints a float64 as `strconv.FormatFloat(v, 'g', -1, 64)`: the shortest digits that round trip,
in `%e` form when the exponent is below -4 or at least 6. The shortest precision whose `%e` output
parses back to `v` gives those digits, and C's `%e` and `%f` then produce Go's layout.
-/
private def printFloatHelper : String := lines [
  "static void goaot_print_float(double v) {",
  "  char buffer[32];",
  "  int precision;",
  "  long exponent;",
  "  if (isnan(v)) { puts(\"NaN\"); return; }",
  "  if (isinf(v)) { puts(v > 0 ? \"+Inf\" : \"-Inf\"); return; }",
  "  for (precision = 0; ; precision++) {",
  "    snprintf(buffer, sizeof buffer, \"%.*e\", precision, v);",
  "    if (precision == 16 || strtod(buffer, NULL) == v) break;",
  "  }",
  "  exponent = strtol(strchr(buffer, 'e') + 1, NULL, 10);",
  "  if (exponent < -4 || exponent >= 6) printf(\"%.*e\\n\", precision, v);",
  "  else printf(\"%.*f\\n\", precision > exponent ? (int)(precision - exponent) : 0, v);",
  "}"]

def emit (program : IR.Program) : String := Id.run do
  let functions : Std.HashMap String IR.Function :=
    program.functions.foldl (fun map function => map.insert function.name function) {}
  let mut divide := false
  let mut unsignedDivide := false
  let mut shift := false
  let mut floatToInt := false
  let mut printFloat := false
  for function in program.functions do
    for block in function.blocks do
      for instruction in block.instructions do
        match instruction with
        | .binary _ op ty .. =>
          if (op == .divide || op == .remainder) && ty.isInteger then
            if ty.isSigned then divide := true else unsignedDivide := true
        | .shift _ _ _ _ countTy _ => if countTy.isSigned then shift := true
        | .convert _ source target _ =>
          if source.kind == .float && target.isInteger then floatToInt := true
        | .print ty _ => if ty.kind == .float then printFloat := true
        | _ => pure ()
  let panics := divide || unsignedDivide || shift
  let mut output := "#include <stdint.h>\n#include <stdio.h>"
  if panics || printFloat then output := output ++ "\n#include <stdlib.h>"
  if printFloat then output := output ++ "\n#include <math.h>\n#include <string.h>"
  for (needed, helper) in [(panics, panicHelper), (divide, divideHelpers),
      (unsignedDivide, unsignedDivideHelpers), (shift, shiftHelper),
      (floatToInt, floatToIntHelpers), (printFloat, printFloatHelper)] do
    if needed then output := output ++ "\n\n" ++ helper
  let mut hasPrototype := false
  for function in program.functions do
    if !Symbol.isEntry function then
      output := emitHeader (output ++ (if hasPrototype then "\n" else "\n\n") ++ "static ") function ++ ";"
      hasPrototype := true
  output := output ++ "\n"
  for function in program.functions do
    output := emitHeader (output ++ "\n" ++ (if Symbol.isEntry function then "" else "static ")) function ++ " {\n"
    -- Slots must remain visible across block braces.
    if let some entry := function.blocks[0]? then
      for instruction in entry.instructions do
        if let .alloca slot ty := instruction then
          output := output ++ s!"  {cType ty} slot_{slot};\n"
    for h : index in [:function.blocks.size] do
      let block := function.blocks[index]
      output := output ++ "  bb" ++ toString index ++ ": {\n"
      output := emitInstructions functions function.parameters output block
      output := emitTerminator function output block.terminator ++ "  }\n"
    output := output ++ "}\n"
  return output

end GoAot.Backend.C
