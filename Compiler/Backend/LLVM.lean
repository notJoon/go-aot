module

public import Compiler.IR
import Compiler.Backend.Symbol
import Std.Data.HashMap

public section

namespace GoAot.Backend.LLVM

-- Collect declarations and deduplicate string globals before any function is emitted.
private def collectRuntimeNeeds (program : IR.Program) :
    Array ByteArray × Std.HashMap ByteArray Nat × Bool := Id.run do
  let mut result := #[]
  let mut indices : Std.HashMap ByteArray Nat := {}
  let mut needsIntFormat := false
  for function in program.functions do
    for block in function.blocks do
      for instruction in block.instructions do
        match instruction with
        | .printString bytes =>
          unless indices.contains bytes do
            indices := indices.insert bytes result.size
            result := result.push bytes
        | .printInt _ => needsIntFormat := true
        | .binary .. | .call .. => pure ()
  return (result, indices, needsIntFormat)

private def hexDigit : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9" | 10 => "A" | 11 => "B"
  | 12 => "C" | 13 => "D" | 14 => "E" | _ => "F"

private def escapeByte (byte : UInt8) : String :=
  let value := byte.toNat
  if 32 <= value && value <= 126 && value != 34 && value != 92 then
    String.singleton (Char.ofNat value)
  else
    "\\" ++ hexDigit (value / 16) ++ hexDigit (value % 16)

private def emitBytes (bytes : ByteArray) : String :=
  String.join (bytes.toList.map escapeByte)

private def operand : IR.Operand → String
  | .value id => s!"%v{id}"
  | .literal value => toString value
  | .argument index => s!"%arg{index}"

private def emitInstructions (stringIndices : Std.HashMap ByteArray Nat)
    (instructions : Array IR.Instruction) (output : Array String) : Array String := Id.run do
  let mut output := output
  for instruction in instructions do
    match instruction with
    | .binary id op left right =>
      let operation := match op with
        | .add => "add i64" | .subtract => "sub i64" | .less => "icmp slt i64"
      output := output.push s!"  %v{id} = {operation} {operand left}, {operand right}\n"
    | .call id name arguments =>
      let values := arguments.toList.map fun value => "i64 " ++ operand value
      output := output.push (s!"  %v{id} = call i64 @{Symbol.function name}(" ++
        String.intercalate ", " values ++ ")\n")
    | .printString bytes =>
      let index := stringIndices[bytes]!
      output := output.push s!"  call void @goaot.print_line(ptr @.str.{index}, i64 {bytes.size})\n"
    | .printInt value =>
      output := output.push s!"  call i32 (ptr, ...) @printf(ptr @.int_format, i64 {operand value})\n"
  return output

private def resultType (function : IR.Function) : String :=
  match function.returnKind with
  | .int => "i64"
  | .void => if Symbol.isEntry function then "i32" else "void"

private def emitTerminator (function : IR.Function) : IR.Terminator → String
  | .br target => s!"  br label %bb{target}\n"
  | .condBr condition ifTrue ifFalse =>
    s!"  br i1 {operand condition}, label %bb{ifTrue}, label %bb{ifFalse}\n"
  | .ret none =>
    if Symbol.returnsVoid function then "  ret void\n"
    else s!"  ret {resultType function} 0\n"
  | .ret (some value) => s!"  ret {resultType function} {operand value}\n"

private def emitFunction (stringIndices : Std.HashMap ByteArray Nat) (output : Array String)
    (function : IR.Function) : Array String := Id.run do
  let parameters := function.parameters.mapIdx fun index _ => s!"i64 %arg{index}"
  let linkage := if Symbol.isEntry function then "" else "internal "
  let mut output := output.push (s!"define {linkage}{resultType function} @{Symbol.function function.name}(" ++
    String.intercalate ", " parameters.toList ++ ") {\n")
  for h : index in [:function.blocks.size] do
    let block := function.blocks[index]
    output := output.push ((if index == 0 then "" else "\n") ++ s!"bb{index}:\n")
    output := (emitInstructions stringIndices block.instructions output).push
      (emitTerminator function block.terminator)
  return output.push "}\n"

def emit (program : IR.Program) : String := Id.run do
  let (strings, stringIndices, needsIntFormat) := collectRuntimeNeeds program

  let mut output : Array String := #[]
  for i in [:strings.size] do
    let bytes := strings[i]!
    output := output.push (s!"@.str.{i} = private unnamed_addr constant [{bytes.size + 1} x i8] c\"" ++
      emitBytes bytes ++ "\\00\"\n")
  if needsIntFormat then
    output := output.push "@.int_format = private unnamed_addr constant [6 x i8] c\"%lld\\0A\\00\"\n"
  if !strings.isEmpty || needsIntFormat then output := output.push "\n"
  if !strings.isEmpty then
    output := output.push "declare i32 @fflush(ptr)\ndeclare i64 @write(i32, ptr, i64)\n"
  if needsIntFormat then output := output.push "declare i32 @printf(ptr, ...)\n"
  if !strings.isEmpty || needsIntFormat then output := output.push "\n"
  -- Darwin exposes `__stdoutp` so `stdout` is not a portable linkable symbol.
  if !strings.isEmpty then output := output.push <|
    "define internal void @goaot.print_line(ptr %bytes, i64 %length) {\n" ++
    "entry:\n  %newline = alloca i8\n  store i8 10, ptr %newline\n" ++
    "  call i32 @fflush(ptr null)\n  br label %loop\n\nloop:\n" ++
    "  %offset = phi i64 [ 0, %entry ], [ %next, %body ]\n" ++
    "  %done = icmp eq i64 %offset, %length\n" ++
    "  br i1 %done, label %exit, label %body\n\nbody:\n" ++
    "  %address = getelementptr i8, ptr %bytes, i64 %offset\n" ++
    "  %remaining = sub i64 %length, %offset\n" ++
    "  %written = call i64 @write(i32 1, ptr %address, i64 %remaining)\n" ++
    "  %next = add i64 %offset, %written\n  %failed = icmp slt i64 %written, 1\n" ++
    "  br i1 %failed, label %exit, label %loop\n\n" ++
    "exit:\n  call i64 @write(i32 1, ptr %newline, i64 1)\n  ret void\n}\n\n"
  for function in program.functions do
    output := (emitFunction stringIndices output function).push "\n"
  return (String.join output.pop.toList)

end GoAot.Backend.LLVM
