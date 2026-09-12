module

public import Compiler.IR

public section

namespace GoAot.Backend.LLVM

private def llvmName (name : String) : String :=
  if name == "main" then name else "go_" ++ name

private def findFunction? (program : IR.Program) (name : String) : Option IR.Function :=
  program.functions.find? fun function => function.name == name

-- Collect declarations and deduplicate string globals before any function is emitted.
private partial def collectRuntimeNeeds (instructions : Array IR.Instruction) :
    Array ByteArray × Bool := Id.run do
  let mut result := #[]
  let mut needsIntFormat := false
  for instruction in instructions do
    match instruction with
    | .printString bytes =>
      unless result.contains bytes do result := result.push bytes
    | .printInt _ => needsIntFormat := true
    | .ifThen _ body =>
      let (strings, nestedNeedsIntFormat) := collectRuntimeNeeds body
      for bytes in strings do
        unless result.contains bytes do result := result.push bytes
      needsIntFormat := needsIntFormat || nestedNeedsIntFormat
    | _ => pure ()
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

private def stringIndex (strings : Array ByteArray) (bytes : ByteArray) : Except String Nat := do
  for i in [:strings.size] do
    if strings[i]! == bytes then return i
  throw "internal error: missing string literal"

private def localIndex (function : IR.Function) (name : String) : Except String Nat := do
  for i in [:function.parameters.size] do
    if function.parameters[i]! == name then return i
  throw s!"unsupported local '{name}'"

-- Recursive emission follows source order and gives each computed value a fresh SSA name.
private partial def emitExpr (program : IR.Program) (function : IR.Function) (nextValue : Nat) :
    IR.Expr → Except String (String × String × Nat)
  | .intLiteral value => do
    if value > 9223372036854775807 then
      throw "integer literal exceeds signed 64-bit range"
    return ("", toString value, nextValue)
  | .local name => return ("", s!"%arg{← localIndex function name}", nextValue)
  | .call name arguments => do
    let some callee := findFunction? program name | throw s!"unknown function '{name}'"
    if name == "main" then throw "main does not return a value"
    if arguments.size != callee.parameters.size then
      throw s!"function '{name}' expects {callee.parameters.size} arguments"
    let mut output := ""
    let mut values := #[]
    let mut next := nextValue
    for argument in arguments do
      let (code, value, after) ← emitExpr program function next argument
      output := output ++ code
      values := values.push ("i64 " ++ value)
      next := after
    let result := s!"%v{next}"
    return (output ++ s!"  {result} = call i64 @{llvmName name}(" ++
      String.intercalate ", " values.toList ++ ")\n", result, next + 1)
  | .binary op left right => do
    let (leftCode, leftValue, next) ← emitExpr program function nextValue left
    let (rightCode, rightValue, next) ← emitExpr program function next right
    let result := s!"%v{next}"
    let operation := match op with
      | .add => "add i64"
      | .subtract => "sub i64"
      | .less => "icmp slt i64"
    return (leftCode ++ rightCode ++
      s!"  {result} = {operation} {leftValue}, {rightValue}\n", result, next + 1)

-- The final flag records whether the current block already owns its required terminator.
private partial def emitInstructions (program : IR.Program) (function : IR.Function)
    (strings : Array ByteArray) (instructions : Array IR.Instruction)
    (nextValue nextBlock : Nat) : Except String (String × Nat × Nat × Bool) := do
  let mut output := ""
  let mut value := nextValue
  let mut block := nextBlock
  let mut terminated := false
  for instruction in instructions do
    unless terminated do
      match instruction with
      | .printString bytes =>
        let index ← stringIndex strings bytes
        output := output ++ s!"  call void @goaot.print_line(ptr @.str.{index}, i64 {bytes.size})\n"
      | .printInt expression =>
        let (code, result, next) ← emitExpr program function value expression
        output := output ++ code ++ s!"  call i32 (ptr, ...) @printf(ptr @.int_format, i64 {result})\n"
        value := next
      | .return expression =>
        if function.name == "main" then throw "main cannot return a value"
        let (code, result, next) ← emitExpr program function value expression
        output := output ++ code ++ s!"  ret i64 {result}\n"
        value := next
        terminated := true
      | .ifThen condition body =>
        let (conditionCode, conditionValue, next) ← emitExpr program function value condition
        let label := block
        let (bodyCode, afterValue, afterBlock, bodyTerminated) ←
          emitInstructions program function strings body next (block + 1)
        output := output ++ conditionCode ++
          s!"  br i1 {conditionValue}, label %if.then.{label}, label %if.end.{label}\n\n" ++
          s!"if.then.{label}:\n" ++ bodyCode ++
          (if bodyTerminated then "" else s!"  br label %if.end.{label}\n") ++
          s!"\nif.end.{label}:\n"
        value := afterValue
        block := afterBlock
  return (output, value, block, terminated)

private def emitFunction (program : IR.Program) (strings : Array ByteArray)
    (function : IR.Function) : Except String String := do
  if function.name == "main" && !function.parameters.isEmpty then
    throw "LLVM backend requires main with no parameters"
  let parameters := function.parameters.mapIdx fun index _ => s!"i64 %arg{index}"
  let linkage := if function.name == "main" then "" else "internal "
  let resultType := if function.name == "main" then "i32" else "i64"
  let (body, _, _, terminated) ← emitInstructions program function strings function.body 0 0
  if function.name != "main" && !terminated then
    throw s!"function '{function.name}' must return a value"
  return s!"define {linkage}{resultType} @{llvmName function.name}(" ++
    String.intercalate ", " parameters.toList ++ ") {\nentry:\n" ++ body ++
    (if function.name == "main" then "  ret i32 0\n" else "") ++ "}\n"

def emit (program : IR.Program) : Except String String := do
  let some main := findFunction? program "main" | throw "LLVM backend requires a main function"
  unless main.parameters.isEmpty do throw "LLVM backend requires main with no parameters"

  let mut strings := #[]
  let mut needsIntFormat := false
  for function in program.functions do
    let (foundStrings, foundNeedsIntFormat) := collectRuntimeNeeds function.body
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
    output := output ++ (← emitFunction program strings function) ++ "\n"
  return (output.dropEnd 1).toString

end GoAot.Backend.LLVM
