module

public import Compiler.IR
import Compiler.Backend.Symbol

public section

namespace GoAot.Backend.C

private def emitParameters (parameters : Array String) : String := Id.run do
  if parameters.isEmpty then return "void"
  let mut result := ""
  for parameter in parameters do
    if !result.isEmpty then result := result ++ ", "
    result := result ++ "int64_t go_" ++ parameter
  return result

private def operand (parameters : Array String) : IR.Operand → String
  | .value id => s!"go_tmp_{id}"
  | .literal value => toString value
  | .argument index => "go_" ++ parameters[index]!

private def hexDigit : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9" | 10 => "A" | 11 => "B"
  | 12 => "C" | 13 => "D" | 14 => "E" | _ => "F"

-- Fixed width escapes stop C from consuming following hexadecimal characters.
private def emitBytes (bytes : ByteArray) : String := Id.run do
  let mut result := ""
  for byte in bytes do
    result := result ++ "\\x" ++ hexDigit (byte.toNat / 16) ++ hexDigit (byte.toNat % 16)
  return result

-- Explicit byte counts preserve embedded NUL values during string output.
private def emitInstructions (parameters : Array String)
    (instructions : Array IR.Instruction) (indent : String) : String := Id.run do
  let mut result := ""
  for instruction in instructions do
    match instruction with
    | .binary id op left right =>
      let symbol := match op with | .add => "+" | .subtract => "-" | .less => "<"
      result := result ++ indent ++
        s!"int64_t go_tmp_{id} = {operand parameters left} {symbol} {operand parameters right};\n"
    | .call id name arguments =>
      result := result ++ indent ++ s!"int64_t go_tmp_{id} = {Symbol.function name}(" ++
        String.intercalate ", " (arguments.toList.map (operand parameters)) ++ ");\n"
    | .printString bytes => result := result ++ indent ++ "fwrite(\"" ++ emitBytes bytes ++
        s!"\", 1, {bytes.size}, stdout); putchar('\\n');\n"
    | .printInt value =>
      result := result ++ indent ++
        "printf(\"%lld\\n\", (long long)" ++ operand parameters value ++ ");\n"
  return result

private def emitTerminator (function : IR.Function) : IR.Terminator → String
  | .br target => s!"    goto bb{target};\n"
  | .condBr condition ifTrue ifFalse =>
    s!"    if ({operand function.parameters condition}) goto bb{ifTrue}; else goto bb{ifFalse};\n"
  | .ret none =>
    if Symbol.returnsVoid function then "    return;\n"
    else "    return 0;\n"
  | .ret (some value) => s!"    return {operand function.parameters value};\n"

private def emitHeader (function : IR.Function) : String :=
  let result := match function.returnKind with
    | .int => "int64_t"
    | .void => if Symbol.isEntry function then "int" else "void"
  result ++ " " ++ Symbol.function function.name ++ "(" ++ emitParameters function.parameters ++ ")"

def emit (program : IR.Program) : String := Id.run do
  let mut output := "#include <stdint.h>\n#include <stdio.h>"
  let mut hasPrototype := false
  for function in program.functions do
    if !Symbol.isEntry function then
      output := output ++ (if hasPrototype then "\n" else "\n\n") ++
        "static " ++ emitHeader function ++ ";"
      hasPrototype := true
  output := output ++ "\n"
  for function in program.functions do
    output := output ++ "\n" ++ (if Symbol.isEntry function then "" else "static ") ++
      emitHeader function ++ " {\n"
    for h : index in [:function.blocks.size] do
      let block := function.blocks[index]
      let body := emitInstructions function.parameters block.instructions "    "
      let terminator := emitTerminator function block.terminator
      output := output ++ s!"  bb{index}: " ++ "{\n" ++ body ++ terminator ++ "  }\n"
    output := output ++ "}\n"
  return output

end GoAot.Backend.C
