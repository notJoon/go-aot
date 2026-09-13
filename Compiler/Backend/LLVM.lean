module

public import Compiler.IR

public section

namespace GoAot.Backend.LLVM

private def llvmName (name : String) : String :=
  if name == "main" then name else "go_" ++ name

-- Collect declarations and deduplicate string globals before any function is emitted.
private def collectRuntimeNeeds (instructions : Array IR.Instruction) :
    Array ByteArray × Bool := Id.run do
  let mut result := #[]
  let mut needsIntFormat := false
  for instruction in instructions do
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

private def emitBytes (bytes : ByteArray) : String := Id.run do
  let mut result := ""
  for byte in bytes do result := result ++ escapeByte byte
  return result

-- Recursive emission follows source order and gives each computed value a fresh SSA name.
private partial def emitExpr (nextValue : Nat) :
    IR.IntExpr → String × String × Nat
  | .literal value => ("", toString value, nextValue)
  | .argument index => ("", s!"%arg{index}", nextValue)
  | .call name arguments => Id.run do
    let mut output := ""
    let mut values := #[]
    let mut next := nextValue
    for argument in arguments do
      let (code, value, after) := emitExpr next argument
      output := output ++ code
      values := values.push ("i64 " ++ value)
      next := after
    let result := s!"%v{next}"
    return (output ++ s!"  {result} = call i64 @{llvmName name}(" ++
      String.intercalate ", " values.toList ++ ")\n", result, next + 1)
  | expression@(.add left right) | expression@(.subtract left right) =>
    let (leftCode, leftValue, next) := emitExpr nextValue left
    let (rightCode, rightValue, next) := emitExpr next right
    let result := s!"%v{next}"
    let operation := match expression with | .add .. => "add i64" | _ => "sub i64"
    (leftCode ++ rightCode ++
      s!"  {result} = {operation} {leftValue}, {rightValue}\n", result, next + 1)

private def emitBoolExpr (nextValue : Nat) : IR.BoolExpr → String × String × Nat
  | .less left right =>
    let (leftCode, leftValue, next) := emitExpr nextValue left
    let (rightCode, rightValue, next) := emitExpr next right
    let result := s!"%v{next}"
    (leftCode ++ rightCode ++
      s!"  {result} = icmp slt i64 {leftValue}, {rightValue}\n", result, next + 1)

private def emitInstructions
    (strings : Array ByteArray) (instructions : Array IR.Instruction)
    (nextValue : Nat) : String × Nat := Id.run do
  let mut output := ""
  let mut value := nextValue
  for instruction in instructions do
    match instruction with
    | .printString bytes =>
      let index := strings.idxOf bytes
      output := output ++ s!"  call void @goaot.print_line(ptr @.str.{index}, i64 {bytes.size})\n"
    | .printInt expression =>
      let (code, result, next) := emitExpr value expression
      output := output ++ code ++ s!"  call i32 (ptr, ...) @printf(ptr @.int_format, i64 {result})\n"
      value := next
  return (output, value)

private def emitTerminator (nextValue : Nat) : IR.Terminator → String × Nat
  | .br target => (s!"  br label %bb{target}\n", nextValue)
  | .condBr condition ifTrue ifFalse =>
    let (code, value, next) := emitBoolExpr nextValue condition
    (code ++ s!"  br i1 {value}, label %bb{ifTrue}, label %bb{ifFalse}\n", next)
  | .ret none => ("  ret i32 0\n", nextValue)
  | .ret (some expression) =>
    let (code, value, next) := emitExpr nextValue expression
    (code ++ s!"  ret i64 {value}\n", next)

private def emitFunction (strings : Array ByteArray)
    (function : IR.Function) : String := Id.run do
  let parameters := function.parameters.mapIdx fun index _ => s!"i64 %arg{index}"
  let linkage := if function.name == "main" then "" else "internal "
  let resultType := if function.name == "main" then "i32" else "i64"
  let mut output := s!"define {linkage}{resultType} @{llvmName function.name}(" ++
    String.intercalate ", " parameters.toList ++ ") {\n"
  let mut next := 0
  for h : index in [:function.blocks.size] do
    let block := function.blocks[index]
    let (body, after) := emitInstructions strings block.instructions next
    let (terminator, after) := emitTerminator after block.terminator
    output := output ++ (if index == 0 then "" else "\n") ++ s!"bb{index}:\n" ++ body ++ terminator
    next := after
  return output ++ "}\n"

def emit (program : IR.Program) : String := Id.run do
  let mut strings := #[]
  let mut needsIntFormat := false
  for function in program.functions do
    for block in function.blocks do
      let (foundStrings, foundNeedsIntFormat) := collectRuntimeNeeds block.instructions
      for bytes in foundStrings do
        unless strings.contains bytes do strings := strings.push bytes
      needsIntFormat := needsIntFormat || foundNeedsIntFormat

  let mut output := ""
  for i in [:strings.size] do
    let bytes := strings[i]!
    output := output ++ s!"@.str.{i} = private unnamed_addr constant [{bytes.size + 1} x i8] c\"" ++
      emitBytes bytes ++ "\\00\"\n"
  if needsIntFormat then
    output := output ++ "@.int_format = private unnamed_addr constant [6 x i8] c\"%lld\\0A\\00\"\n"
  if !strings.isEmpty || needsIntFormat then output := output ++ "\n"
  if !strings.isEmpty then output := output ++ "declare i32 @putchar(i32)\n"
  if needsIntFormat then output := output ++ "declare i32 @printf(ptr, ...)\n"
  if !strings.isEmpty || needsIntFormat then output := output ++ "\n"
  -- Darwin exposes `__stdoutp` so `stdout` is not a portable linkable symbol.
  -- A C ABI loop preserves NUL bytes and ordering with `printf` without target symbols.
  -- TODO: Use target specific `fwrite` with its stdout handle or POSIX `write` when string output performance matters.
  if !strings.isEmpty then output := output ++
    "define internal void @goaot.print_line(ptr %bytes, i64 %length) {\n" ++
    "entry:\n  br label %loop\n\nloop:\n" ++
    "  %index = phi i64 [ 0, %entry ], [ %next, %body ]\n" ++
    "  %done = icmp eq i64 %index, %length\n" ++
    "  br i1 %done, label %exit, label %body\n\nbody:\n" ++
    "  %address = getelementptr i8, ptr %bytes, i64 %index\n" ++
    "  %byte = load i8, ptr %address\n  %char = zext i8 %byte to i32\n" ++
    "  call i32 @putchar(i32 %char)\n  %next = add i64 %index, 1\n" ++
    "  br label %loop\n\nexit:\n  call i32 @putchar(i32 10)\n  ret void\n}\n\n"
  for function in program.functions do
    output := output ++ emitFunction strings function ++ "\n"
  return (output.dropEnd 1).toString

end GoAot.Backend.LLVM
