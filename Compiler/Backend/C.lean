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
private partial def emitExpr (indent : String) (nextTemp : Nat) :
    IR.Expr → String × String × Nat
  | .intLiteral value => ("", toString value, nextTemp)
  | .local name => ("", "go_" ++ name, nextTemp)
  | .call name arguments => Id.run do
    let mut output := ""
    let mut values := #[]
    let mut next := nextTemp
    for argument in arguments do
      let (code, value, after) := emitExpr indent next argument
      output := output ++ code
      values := values.push value
      next := after
    let result := s!"go_tmp_{next}"
    return (output ++ indent ++ s!"int64_t {result} = {cName name}(" ++
      String.intercalate ", " values.toList ++ ");\n", result, next + 1)
  | .binary op left right =>
    let (leftCode, leftValue, next) := emitExpr indent nextTemp left
    let (rightCode, rightValue, next) := emitExpr indent next right
    let result := s!"go_tmp_{next}"
    let symbol := match op with | .add => "+" | .subtract => "-" | .less => "<"
    (leftCode ++ rightCode ++ indent ++
      s!"int64_t {result} = {leftValue} {symbol} {rightValue};\n", result, next + 1)

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
private partial def emitInstructions (instructions : Array IR.Instruction) (indent : String)
    (nextTemp : Nat) : String × Nat :=
  Id.run do
    let mut result := ""
    let mut next := nextTemp
    for instruction in instructions do
      match instruction with
      | .printString bytes => result := result ++ indent ++ "fwrite(\"" ++ emitBytes bytes ++
          s!"\", 1, {bytes.size}, stdout); putchar('\\n');\n"
      | .printInt expression =>
        let (code, value, after) := emitExpr indent next expression
        result := result ++ code ++ indent ++
          "printf(\"%lld\\n\", (long long)" ++ value ++ ");\n"
        next := after
      | .return expression =>
        let (code, value, after) := emitExpr indent next expression
        result := result ++ code ++ indent ++ "return " ++ value ++ ";\n"
        next := after
      | .ifThen condition body =>
        let (conditionCode, conditionValue, afterCondition) := emitExpr indent next condition
        let (body, afterBody) := emitInstructions body (indent ++ "  ") afterCondition
        result := result ++ conditionCode ++ indent ++ "if (" ++ conditionValue ++ ") {\n" ++
          body ++ indent ++ "}\n"
        next := afterBody
    return (result, next)

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
    let (body, _) := emitInstructions function.body "  " 0
    output := output ++ "\n" ++ (if function.name == "main" then "" else "static ") ++
      emitHeader function ++ " {\n" ++ body
    if function.name == "main" then output := output ++ "  return 0;\n"
    output := output ++ "}\n"
  return output

end GoAot.Backend.C
