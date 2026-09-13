module

public import Compiler.IR

public section

namespace GoAot.Backend.C

private def cName (name : String) : String :=
  if name == "main" then name else "go_" ++ name

private def emitParameters (parameters : Array String) : String := Id.run do
  if parameters.isEmpty then return "void"
  let mut result := ""
  for parameter in parameters do
    if !result.isEmpty then result := result ++ ", "
    result := result ++ "int64_t go_" ++ parameter
  return result

-- Named temporaries preserve Go evaluation order because C leaves operand and argument order unspecified.
private partial def emitExpr (parameters : Array String) (indent : String) (nextTemp : Nat) :
    IR.IntExpr → String × String × Nat
  | .literal value => ("", toString value, nextTemp)
  | .argument index => ("", "go_" ++ parameters[index]!, nextTemp)
  | .call name arguments => Id.run do
    let mut output := ""
    let mut values := #[]
    let mut next := nextTemp
    for argument in arguments do
      let (code, value, after) := emitExpr parameters indent next argument
      output := output ++ code
      values := values.push value
      next := after
    let result := s!"go_tmp_{next}"
    return (output ++ indent ++ s!"int64_t {result} = {cName name}(" ++
      String.intercalate ", " values.toList ++ ");\n", result, next + 1)
  | expression@(.add left right) | expression@(.subtract left right) =>
    let (leftCode, leftValue, next) := emitExpr parameters indent nextTemp left
    let (rightCode, rightValue, next) := emitExpr parameters indent next right
    let result := s!"go_tmp_{next}"
    let symbol := match expression with | .add .. => "+" | _ => "-"
    (leftCode ++ rightCode ++ indent ++
      s!"int64_t {result} = {leftValue} {symbol} {rightValue};\n", result, next + 1)

private def emitBoolExpr (parameters : Array String) (indent : String) (nextTemp : Nat) :
    IR.BoolExpr → String × String × Nat
  | .less left right =>
    let (leftCode, leftValue, next) := emitExpr parameters indent nextTemp left
    let (rightCode, rightValue, next) := emitExpr parameters indent next right
    let result := s!"go_tmp_{next}"
    (leftCode ++ rightCode ++ indent ++
      s!"int64_t {result} = {leftValue} < {rightValue};\n", result, next + 1)

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
    (instructions : Array IR.Instruction) (indent : String)
    (nextTemp : Nat) : String × Nat :=
  Id.run do
    let mut result := ""
    let mut next := nextTemp
    for instruction in instructions do
      match instruction with
      | .printString bytes => result := result ++ indent ++ "fwrite(\"" ++ emitBytes bytes ++
          s!"\", 1, {bytes.size}, stdout); putchar('\\n');\n"
      | .printInt expression =>
        let (code, value, after) := emitExpr parameters indent next expression
        result := result ++ code ++ indent ++
          "printf(\"%lld\\n\", (long long)" ++ value ++ ");\n"
        next := after
    return (result, next)

private def emitTerminator (parameters : Array String) (nextTemp : Nat) :
    IR.Terminator → String × Nat
  | .br target => (s!"    goto bb{target};\n", nextTemp)
  | .condBr condition ifTrue ifFalse =>
    let (code, value, next) := emitBoolExpr parameters "    " nextTemp condition
    (code ++ s!"    if ({value}) goto bb{ifTrue}; else goto bb{ifFalse};\n", next)
  | .ret none => ("    return 0;\n", nextTemp)
  | .ret (some expression) =>
    let (code, value, next) := emitExpr parameters "    " nextTemp expression
    (code ++ s!"    return {value};\n", next)

private def emitHeader (function : IR.Function) : String :=
  let result := if function.name == "main" then "int" else "int64_t"
  result ++ " " ++ cName function.name ++ "(" ++ emitParameters function.parameters ++ ")"

def emit (program : IR.Program) : String := Id.run do
  let mut output := "#include <stdint.h>\n#include <stdio.h>"
  let mut hasPrototype := false
  for function in program.functions do
    if function.name != "main" then
      output := output ++ (if hasPrototype then "\n" else "\n\n") ++
        "static " ++ emitHeader function ++ ";"
      hasPrototype := true
  output := output ++ "\n"
  for function in program.functions do
    output := output ++ "\n" ++ (if function.name == "main" then "" else "static ") ++
      emitHeader function ++ " {\n"
    let mut next := 0
    for h : index in [:function.blocks.size] do
      let block := function.blocks[index]
      let (body, after) := emitInstructions function.parameters block.instructions "    " next
      let (terminator, after) := emitTerminator function.parameters after block.terminator
      output := output ++ s!"  bb{index}: " ++ "{\n" ++ body ++ terminator ++ "  }\n"
      next := after
    output := output ++ "}\n"
  return output

end GoAot.Backend.C
