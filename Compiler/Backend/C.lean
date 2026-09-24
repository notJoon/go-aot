module

public import Compiler.IR
import Compiler.Backend.Symbol
import Std.Data.HashSet

public section

namespace GoAot.Backend.C

private def emitParameters (output : String) (parameters : Array String) : String := Id.run do
  if parameters.isEmpty then return output ++ "void"
  let mut output := output
  for h : index in [:parameters.size] do
    if index != 0 then output := output ++ ", "
    output := output ++ "int64_t arg_" ++ parameters[index]
  return output

private def emitOperand (parameters : Array String) (output : String) : IR.Operand → String
  | .value id => output ++ "tmp_" ++ toString id
  | .literal value => output ++ toString value
  | .argument index => output ++ "arg_" ++ parameters[index]!

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
      | .store _ _ value | .printInt value => add used value
      | .binary _ _ left right => add (add used left) right
      | .call _ _ arguments | .callVoid _ arguments => arguments.foldl add used
      | .alloca .. | .load .. | .printString _ => used
  return match block.terminator with
    | .condBr condition .. => add used condition
    | .ret (some value) => add used value
    | .br _ | .ret none => used

-- Explicit byte counts preserve embedded NUL values during string output.
private def emitInstructions (parameters : Array String)
    (output : String) (block : IR.Block) : String := Id.run do
  let used := usedValues block
  let mut output := output
  for instruction in block.instructions do
    match instruction with
    | .alloca .. => pure () -- Slot declarations are emitted outside the block braces.
    | .load id slot _ =>
      output := output ++ s!"    int64_t tmp_{id} = slot_{slot};\n"
    | .store slot _ value =>
      output := emitOperand parameters (output ++ s!"    slot_{slot} = ") value ++ ";\n"
    | .binary id op left right =>
      let symbol := match op with | .add => "+" | .subtract => "-" | .less => "<"
      output := emitOperand parameters (output ++ "    int64_t tmp_" ++ toString id ++ " = ") left
      output := emitOperand parameters (output ++ " " ++ symbol ++ " ") right ++ ";\n"
    | .call id name arguments =>
      output := output ++ "    "
      if used.contains id then output := output ++ "int64_t tmp_" ++ toString id ++ " = "
      output := output ++ Symbol.function name ++ "("
      for h : index in [:arguments.size] do
        if index != 0 then output := output ++ ", "
        output := emitOperand parameters output arguments[index]
      output := output ++ ");\n"
    | .callVoid name arguments =>
      output := output ++ "    " ++ Symbol.function name ++ "("
      for h : index in [:arguments.size] do
        if index != 0 then output := output ++ ", "
        output := emitOperand parameters output arguments[index]
      output := output ++ ");\n"
    | .printString bytes =>
      output := emitBytes (output ++ "    fwrite(\"") bytes ++
        "\", 1, " ++ toString bytes.size ++ ", stdout); putchar('\\n');\n"
    | .printInt value =>
      output := emitOperand parameters (output ++ "    printf(\"%lld\\n\", (long long)") value ++ ");\n"
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
    | .int => "int64_t"
    | .void => if Symbol.isEntry function then "int" else "void"
  emitParameters (output ++ result ++ " " ++ Symbol.function function.name ++ "(") function.parameters ++ ")"

def emit (program : IR.Program) : String := Id.run do
  let mut output := "#include <stdint.h>\n#include <stdio.h>"
  let mut hasPrototype := false
  for function in program.functions do
    if !Symbol.isEntry function then
      output := emitHeader (output ++ (if hasPrototype then "\n" else "\n\n") ++ "static ") function ++ ";"
      hasPrototype := true
  output := output ++ "\n"
  for function in program.functions do
    output := emitHeader (output ++ "\n" ++ (if Symbol.isEntry function then "" else "static ")) function ++ " {\n"
    -- Slots must remain visible across block braces. Bool slots also use int64_t,
    -- matching the existing representation of comparison results as 0 or 1.
    if let some entry := function.blocks[0]? then
      for instruction in entry.instructions do
        if let .alloca slot _ := instruction then
          output := output ++ s!"  int64_t slot_{slot};\n"
    for h : index in [:function.blocks.size] do
      let block := function.blocks[index]
      output := output ++ "  bb" ++ toString index ++ ": {\n"
      output := emitInstructions function.parameters output block
      output := emitTerminator function output block.terminator ++ "  }\n"
    output := output ++ "}\n"
  return output

end GoAot.Backend.C
