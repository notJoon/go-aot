module

public import Compiler.IR

public section

namespace GoAot.Backend.LLVM

private def llvmName (name : String) : String :=
  if name == "main" then name else "go_" ++ name

-- Collect declarations and deduplicate string globals before any function is emitted.
private def collectRuntimeNeeds (program : IR.Program) :
    Array ByteArray × Bool := Id.run do
  let mut result := #[]
  let mut needsIntFormat := false
  for function in program.functions do
    for block in function.blocks do
      for instruction in block.instructions do
        match instruction with
        | .printString bytes =>
          unless result.contains bytes do result := result.push bytes
        | .printInt _ => needsIntFormat := true
  return (result, needsIntFormat)

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

-- Recursive emission follows source order and gives each computed value a fresh SSA name.
private partial def emitExpr (output : Array String) (nextValue : Nat) :
    IR.IntExpr → Array String × String × Nat
  | .literal value => (output, toString value, nextValue)
  | .argument index => (output, s!"%arg{index}", nextValue)
  | .call name arguments => Id.run do
    let mut output := output
    let mut values := #[]
    let mut next := nextValue
    for argument in arguments do
      let (after, value, afterValue) := emitExpr output next argument
      output := after
      values := values.push ("i64 " ++ value)
      next := afterValue
    let result := s!"%v{next}"
    return (output.push (s!"  {result} = call i64 @{llvmName name}(" ++
      String.intercalate ", " values.toList ++ ")\n"), result, next + 1)
  | expression@(.add left right) | expression@(.subtract left right) =>
    let (output, leftValue, next) := emitExpr output nextValue left
    let (output, rightValue, next) := emitExpr output next right
    let result := s!"%v{next}"
    let operation := match expression with | .add .. => "add i64" | _ => "sub i64"
    (output.push s!"  {result} = {operation} {leftValue}, {rightValue}\n", result, next + 1)

private def emitBoolExpr (output : Array String) (nextValue : Nat) :
    IR.BoolExpr → Array String × String × Nat
  | .less left right =>
    let (output, leftValue, next) := emitExpr output nextValue left
    let (output, rightValue, next) := emitExpr output next right
    let result := s!"%v{next}"
    (output.push s!"  {result} = icmp slt i64 {leftValue}, {rightValue}\n", result, next + 1)

private def emitInstructions (strings : Array ByteArray)
    (instructions : Array IR.Instruction) (output : Array String)
    (nextValue : Nat) : Array String × Nat := Id.run do
  let mut output := output
  let mut value := nextValue
  for instruction in instructions do
    match instruction with
    | .printString bytes =>
      let index := strings.idxOf bytes
      output := output.push s!"  call void @goaot.print_line(ptr @.str.{index}, i64 {bytes.size})\n"
    | .printInt expression =>
      let (after, result, next) := emitExpr output value expression
      output := after.push s!"  call i32 (ptr, ...) @printf(ptr @.int_format, i64 {result})\n"
      value := next
  return (output, value)

private def emitTerminator (output : Array String) (nextValue : Nat) :
    IR.Terminator → Array String × Nat
  | .br target => (output.push s!"  br label %bb{target}\n", nextValue)
  | .condBr condition ifTrue ifFalse =>
    let (output, value, next) := emitBoolExpr output nextValue condition
    (output.push s!"  br i1 {value}, label %bb{ifTrue}, label %bb{ifFalse}\n", next)
  | .ret none => (output.push "  ret i32 0\n", nextValue)
  | .ret (some expression) =>
    let (output, value, next) := emitExpr output nextValue expression
    (output.push s!"  ret i64 {value}\n", next)

private def emitFunction (strings : Array ByteArray) (output : Array String)
    (function : IR.Function) : Array String := Id.run do
  let parameters := function.parameters.mapIdx fun index _ => s!"i64 %arg{index}"
  let linkage := if function.name == "main" then "" else "internal "
  let resultType := if function.name == "main" then "i32" else "i64"
  let mut output := output.push (s!"define {linkage}{resultType} @{llvmName function.name}(" ++
    String.intercalate ", " parameters.toList ++ ") {\n")
  let mut next := 0
  for h : index in [:function.blocks.size] do
    let block := function.blocks[index]
    output := output.push ((if index == 0 then "" else "\n") ++ s!"bb{index}:\n")
    let (body, after) := emitInstructions strings block.instructions output next
    let (terminated, after) := emitTerminator body after block.terminator
    output := terminated
    next := after
  return output.push "}\n"

def emit (program : IR.Program) : String := Id.run do
  let (strings, needsIntFormat) := collectRuntimeNeeds program

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
    output := (emitFunction strings output function).push "\n"
  return (String.join output.pop.toList)

end GoAot.Backend.LLVM
