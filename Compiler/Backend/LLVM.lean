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
        | _ => pure ()
  return (result, indices, needsIntFormat)

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

private def emitOperand (output : String) : IR.Operand → String
  | .value id => output ++ "%v" ++ toString id
  | .literal value => output ++ toString value
  | .argument index => output ++ "%arg" ++ toString index

private def emitInstructions (stringIndices : Std.HashMap ByteArray Nat)
    (output : String) (instructions : Array IR.Instruction) : String := Id.run do
  let mut output := output
  for instruction in instructions do
    match instruction with
    | .alloca slot kind =>
      output := output ++ s!"  %slot{slot} = alloca {if kind == .int then "i64" else "i1"}\n"
    | .load id slot kind =>
      output := output ++ s!"  %v{id} = load {if kind == .int then "i64" else "i1"}, ptr %slot{slot}\n"
    | .store slot kind value =>
      output := emitOperand (output ++ s!"  store {if kind == .int then "i64" else "i1"} ") value ++
        s!", ptr %slot{slot}\n"
    | .binary id op left right =>
      let operation := match op with
        | .add => "add i64" | .subtract => "sub i64" | .less => "icmp slt i64"
      output := emitOperand (output ++ "  %v" ++ toString id ++ " = " ++ operation ++ " ") left
      output := emitOperand (output ++ ", ") right ++ "\n"
    | .call id name arguments =>
      output := output ++ "  %v" ++ toString id ++ " = call i64 @" ++ Symbol.function name ++ "("
      for h : index in [:arguments.size] do
        if index != 0 then output := output ++ ", "
        output := emitOperand (output ++ "i64 ") arguments[index]
      output := output ++ ")\n"
    | .callVoid name arguments =>
      output := output ++ "  call void @" ++ Symbol.function name ++ "("
      for h : index in [:arguments.size] do
        if index != 0 then output := output ++ ", "
        output := emitOperand (output ++ "i64 ") arguments[index]
      output := output ++ ")\n"
    | .printString bytes =>
      let index := stringIndices[bytes]!
      output := output ++ "  call void @goaot.print_line(ptr @.str." ++ toString index ++
        ", i64 " ++ toString bytes.size ++ ")\n"
    | .printInt value =>
      output := emitOperand (output ++ "  call i32 (ptr, ...) @printf(ptr @.int_format, i64 ") value ++ ")\n"
  return output

private def resultType (function : IR.Function) : String :=
  match function.returnKind with
  | .int => "i64"
  | .void => if Symbol.isEntry function then "i32" else "void"

private def emitTerminator (function : IR.Function) (output : String) : IR.Terminator → String
  | .br target => output ++ "  br label %bb" ++ toString target ++ "\n"
  | .condBr condition ifTrue ifFalse =>
    emitOperand (output ++ "  br i1 ") condition ++ ", label %bb" ++ toString ifTrue ++
      ", label %bb" ++ toString ifFalse ++ "\n"
  | .ret none =>
    if Symbol.returnsVoid function then output ++ "  ret void\n"
    else output ++ "  ret " ++ resultType function ++ " 0\n"
  | .ret (some value) => emitOperand (output ++ "  ret " ++ resultType function ++ " ") value ++ "\n"

private def emitFunction (stringIndices : Std.HashMap ByteArray Nat) (output : String)
    (function : IR.Function) : String := Id.run do
  let linkage := if Symbol.isEntry function then "" else "internal "
  let mut output := output ++ "define " ++ linkage ++ resultType function ++ " @" ++ Symbol.function function.name ++ "("
  for index in [:function.parameters.size] do
    if index != 0 then output := output ++ ", "
    output := output ++ "i64 %arg" ++ toString index
  output := output ++ ") {\n"
  for h : index in [:function.blocks.size] do
    let block := function.blocks[index]
    if index != 0 then output := output ++ "\n"
    output := output ++ "bb" ++ toString index ++ ":\n"
    output := emitInstructions stringIndices output block.instructions
    output := emitTerminator function output block.terminator
  return output ++ "}\n"

def emit (program : IR.Program) : String := Id.run do
  let (strings, stringIndices, needsIntFormat) := collectRuntimeNeeds program

  let mut output := ""
  for h : i in [:strings.size] do
    let bytes := strings[i]
    output := emitBytes (output ++ "@.str." ++ toString i ++ " = private unnamed_addr constant [" ++
      toString (bytes.size + 1) ++ " x i8] c\"") bytes ++ "\\00\"\n"
  if needsIntFormat then
    output := output ++ "@.int_format = private unnamed_addr constant [6 x i8] c\"%lld\\0A\\00\"\n"
  if !strings.isEmpty || needsIntFormat then output := output ++ "\n"
  if !strings.isEmpty then
    output := output ++ "declare i32 @fflush(ptr)\ndeclare i64 @write(i32, ptr, i64)\n"
  if needsIntFormat then output := output ++ "declare i32 @printf(ptr, ...)\n"
  if !strings.isEmpty || needsIntFormat then output := output ++ "\n"
  -- Darwin exposes `__stdoutp` so `stdout` is not a portable linkable symbol.
  if !strings.isEmpty then output := output ++
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
  for h : index in [:program.functions.size] do
    if index != 0 then output := output ++ "\n"
    output := emitFunction stringIndices output program.functions[index]
  return output

end GoAot.Backend.LLVM
