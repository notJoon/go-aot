import Compiler.Parser.Go
import Compiler.Lowering
import Compiler.Check
import Compiler.Backend.LLVM
import Compiler.IR.Verify
import Compiler.Lowering.Builder

open GoAot

private def sourceView (source : String) (text : String.Slice) (span : Span)
    (expected : String) : Bool :=
  text.str == source && text.startInclusive.offset.byteIdx == span.start &&
    text.endExclusive.offset.byteIdx == span.stop && text == expected.toSlice

#guard Id.run do
  let source := "package main\nfunc 계산(값 int) int { return 계산(값 + 1_000) }\n"
  let .ok file := parse (Source.ofString source) | return false
  let some function := file.functions[0]? | return false
  let some parameter := function.parameters[0]? | return false
  let some resultType := function.results[0]? | return false
  let some (Syntax.Stmt.return #[(.call callee arguments _)] _) := function.body[0]? | return false
  let some (Syntax.Expr.binary .add (.identifier name) (.intLiteral text span) _) := arguments[0]?
    | return false
  return [(file.packageName, "main"), (function.name, "계산"), (parameter.name, "값"),
    (parameter.typeName, "int"), (resultType, "int"), (callee, "계산"), (name, "값")].all
      (fun (name, expected) => sourceView source name.text name.span expected) &&
    sourceView source text span "1_000" && text.toNat? == some 1000

-- Any identifier reaches LLVM, quoted when it is not plain ASCII (#15).
/--
info: "fib" @go_fib
"main" @main
"go_main" @go_go_main
"_" @go__
"계산" @"go_\EA\B3\84\EC\82\B0"
"a١" @"go_a\D9\A1"
"a\"b" @"go_a\22b"
"a\\22b" @"go_a\5C22b"
"a-b" @"go_a-b"
"" @go_
-/
#guard_msgs in
#eval show IO Unit from do
  let names := ["fib", "main", "go_main", "_", "계산", "a١", "a\"b", "a\\22b", "a-b", ""]
  for name in names do IO.println s!"{repr name} {Backend.Symbol.function name}"
  unless (names.map Backend.Symbol.function).eraseDups.length == names.length do
    IO.println "two names share a symbol"

#guard match (parse (Source.ofString
    "package main\nfunc f() int { return 1 }\nfunc f() int { return 2 }\nfunc main() {}\n")).bind Check.check with
  | .error error => error == ⟨.check, some ⟨44, 45⟩, "duplicate function 'f'"⟩
  | .ok _ => false

-- Existing phase interfaces reject mixed inputs without result wrappers.
example : Source → Except Diagnostic Syntax.File := parse
example : Syntax.File → Except Diagnostic Checked.File := Check.check
example : Checked.File → Except Diagnostic IR.Program := Lowering.lower
#check_failure fun (raw : Array Token) => parse raw
#check_failure fun (source : Source) => Check.check source
#check_failure fun (file : Syntax.File) => Backend.LLVM.emit file

private def intValue : IR.Operand := .literal 1
private def comparison : IR.Instruction := .binary 0 .less .int intValue intValue
private def boolValue : IR.Operand := .value 0
#check_failure (show IR.Block from { instructions := #[] })

-- The backend cannot fail on verified IR.
example : IR.Program → String := Backend.LLVM.emit
example : IR.Program → Except IR.VerifyError Unit := IR.verify

private def mainFunction : IR.Function := ⟨"main", #[], #[], #[⟨#[], .ret #[]⟩]⟩
private def intFunction : IR.Function :=
  ⟨"f", #[⟨"x", .int⟩], #[.int], #[⟨#[], .ret #[(.argument 0)]⟩]⟩

/-- `ok`, or where verification failed and why, without the constant `internal error` prefix. -/
private def verified (program : IR.Program) : String :=
  match IR.verify program with
  | .ok () => "ok"
  | .error error =>
    let text := (error.render.dropPrefix "internal error: invalid IR").copy
    ((text.dropPrefix " in ").dropPrefix ": ").copy

private def report (programs : List IR.Program) : IO Unit :=
  for program in programs do IO.println (verified program)

/-- `main` with these blocks, followed by other functions. -/
private def inMain (blocks : Array IR.Block) (others : Array IR.Function := #[]) : IR.Program :=
  ⟨#[{ mainFunction with blocks }] ++ others⟩

private def definition : IR.Instruction := .binary 0 .add .int intValue intValue

-- Function names, parameters, and the program's function set.
/--
info: ok
function 'f': duplicate parameter 'x'
function 'f', block 0, terminator: return must have 0 operands
function 'f': function must have an entry block
function 'f', block 0, terminator: return must have 1 operands
expected main function
expected main function
function 'f': duplicate function 'f'
function 'main': main must have no parameters or return value
function 'main': main must have no parameters or return value
-/
#guard_msgs in
#eval report ([⟨#[mainFunction, intFunction]⟩] ++
  [{ intFunction with parameters := #[⟨"x", .int⟩, ⟨"x", .int⟩] },
    { intFunction with results := #[] }, { intFunction with blocks := #[] },
    { intFunction with blocks := #[⟨#[], .ret #[]⟩] }].map (⟨#[mainFunction, ·]⟩) ++
  [⟨#[]⟩, ⟨#[intFunction]⟩, ⟨#[mainFunction, intFunction, intFunction]⟩,
    ⟨#[{ mainFunction with parameters := #[⟨"x", .int⟩] }]⟩,
    ⟨#[{ mainFunction with results := #[.int] }]⟩])

-- Branch targets and returns.
/--
info: function 'main', block 0, terminator: branch target 1 is out of range
function 'main', block 0, terminator: branch to entry block is not allowed
function 'main', block 0, terminator: branch target 1 is out of range
function 'main', block 0, terminator: return must have 0 operands
function 'main', block 0, terminator: branch to entry block is not allowed
function 'main', block 0, terminator: branch target 2 is out of range
ok
-/
#guard_msgs in
#eval report (
  [IR.Terminator.br 1, .br 0, .condBr boolValue 1 2, .ret #[intValue]].map
    (fun terminator => inMain #[⟨#[comparison], terminator⟩]) ++
  [inMain #[⟨#[comparison], .condBr boolValue 1 0⟩, ⟨#[], .ret #[]⟩],
    inMain #[⟨#[comparison], .condBr boolValue 1 2⟩, ⟨#[], .ret #[]⟩],
    inMain #[⟨#[], .br 1⟩, ⟨#[comparison], .condBr boolValue 1 1⟩,
      ⟨#[.printString (ByteArray.mk #[0, 255]), .print .int (.literal 9223372036854775807)], .ret #[]⟩]])

-- Calls, literals, and arguments, wherever they appear.
/--
info: function 'main', block 0, instruction 0: integer literal 9223372036854775808 is out of range for int
function 'main', block 0, instruction 0: argument index 0 is out of range
function 'main', block 0, instruction 0: unknown function 'missing'
function 'main', block 0, instruction 0: function 'f' expects 1 arguments
function 'main', block 0, instruction 0: cannot call 'main'
function 'main', block 0, instruction 0: cannot call 'main'
function 'main', block 0, instruction 0: call to 'f' must define 1 results
function 'main', block 0, instruction 0: argument index 0 is out of range
function 'main', block 0, instruction 0: argument index 0 is out of range
function 'main', block 1, instruction 0: argument index 0 is out of range
function 'f', block 0, terminator: argument index 1 is out of range
function 'main', block 0, instruction 0: argument index 0 is out of range
ok
-/
#guard_msgs in
#eval report (
  [IR.Instruction.print .int (.literal 9223372036854775808), .print .int (.argument 0),
    .call #[0] "missing" #[], .call #[0] "f" #[], .call #[0] "main" #[], .call #[] "main" #[],
    .call #[] "f" #[intValue], .call #[0] "f" #[.argument 0],
    .binary 0 .add .int intValue (.argument 0)].map
    (fun instruction => inMain #[⟨#[instruction], .ret #[]⟩] #[intFunction]) ++
  [inMain #[⟨#[], .ret #[]⟩, ⟨#[.print .int (.argument 0)], .ret #[]⟩],
    ⟨#[mainFunction, { intFunction with blocks := #[⟨#[], .ret #[(.argument 1)]⟩] }]⟩,
    inMain #[⟨#[.binary 0 .less .int (.argument 0) intValue], .condBr boolValue 1 1⟩, ⟨#[], .ret #[]⟩],
    ⟨#[mainFunction,
      { intFunction with blocks := #[⟨#[.call #[0] "g" #[.argument 0]], .ret #[(.value 0)]⟩] },
      { intFunction with name := "g", blocks := #[⟨#[.call #[0] "f" #[.argument 0]], .ret #[(.value 0)]⟩] }]⟩])

-- A value is defined once per function and used later in the same block, with its kind.
/--
info: function 'main', block 0, instruction 0: value 42 is not defined earlier in this block
function 'main', block 0, instruction 0: value 0 is not defined earlier in this block
function 'main', block 0, instruction 0: value 0 is not defined earlier in this block
function 'main', block 0, instruction 1: value 0 is defined more than once
function 'main', block 1, instruction 0: value 0 is defined more than once
function 'main', block 1, instruction 0: value 0 is not defined earlier in this block
function 'main', block 0, terminator: expected bool operand
function 'main', block 0, instruction 1: expected int operand
function 'main', block 0, instruction 1: expected int operand
function 'main', block 0, instruction 1: expected int operand
function 'main', block 0, instruction 1: argument index 0 is out of range
ok
function 'f', block 0, terminator: expected int operand
-/
#guard_msgs in
#eval report (
  [#[⟨#[.print .int (.value 42)], .ret #[]⟩],
    #[⟨#[.print .int (.value 0), definition], .ret #[]⟩],
    #[⟨#[.binary 0 .add .int (.value 0) intValue], .ret #[]⟩],
    #[⟨#[definition, definition], .ret #[]⟩],
    #[⟨#[definition], .br 1⟩, ⟨#[definition], .ret #[]⟩],
    #[⟨#[definition], .br 1⟩, ⟨#[.print .int (.value 0)], .ret #[]⟩],
    #[⟨#[], .condBr intValue 1 1⟩, ⟨#[], .ret #[]⟩],
    #[⟨#[comparison, .binary 1 .add .int boolValue intValue], .ret #[]⟩],
    #[⟨#[comparison, .call #[1] "f" #[boolValue]], .ret #[]⟩],
    #[⟨#[comparison, .print .int boolValue], .ret #[]⟩],
    #[⟨#[.printString ByteArray.empty, .print .int (.argument 0)], .ret #[]⟩],
    #[⟨#[.binary 100 .add .int intValue intValue, .binary 7 .subtract .int (.value 100) intValue,
      .call #[42] "f" #[.value 7], .print .int (.value 42)], .ret #[]⟩]].map
    (inMain · #[intFunction]) ++
  [⟨#[mainFunction, { intFunction with blocks := #[⟨#[comparison], .ret #[boolValue]⟩] }]⟩])
#guard match IR.verify (inMain #[⟨#[], .br 0⟩]) with
  | .error error => error.render ==
    "internal error: invalid IR in function 'main', block 0, terminator: branch to entry block is not allowed"
  | .ok _ => false

-- Only equality accepts bool operands, and both operands must have the operator kind.
/--
info: ok
function 'main', block 0, instruction 0: operator is not defined on bool
function 'main', block 0, instruction 0: operator is not defined on bool
function 'main', block 0, instruction 0: expected bool operand
function 'main', block 0, instruction 0: expected int operand
-/
#guard_msgs in
#eval report (
  [inMain #[⟨#[.binary 0 .notEqual .bool (.boolLiteral true) (.boolLiteral false)], .condBr (.value 0) 1 1⟩,
    ⟨#[], .ret #[]⟩]] ++
  [IR.Instruction.binary 0 .add .bool (.boolLiteral true) (.boolLiteral true),
    .binary 0 .less .bool (.boolLiteral true) (.boolLiteral true),
    .binary 0 .equal .bool (.boolLiteral true) intValue,
    .binary 0 .equal .int intValue (.boolLiteral true)].map (fun instruction => inMain #[⟨#[instruction], .ret #[]⟩]))

-- Literals take the type of their use, and conversions and shifts check their operand types.
/--
info: ok
function 'main', block 0, instruction 0: integer literal 128 is out of range for int8
function 'main', block 0, instruction 0: integer literal -1 is out of range for uint8
function 'main', block 0, instruction 0: expected int operand
function 'main', block 0, instruction 0: expected float64 operand
function 'main', block 0, instruction 0: float literal must be finite
function 'main', block 0, instruction 0: operator is not defined on float64
function 'main', block 0, instruction 0: operator is not defined on float64
function 'main', block 0, instruction 0: shift operands must be integers
function 'main', block 0, instruction 0: shift operands must be integers
function 'main', block 0, instruction 0: cannot convert bool to int
function 'main', block 0, instruction 0: integer literal 300 is out of range for int8
-/
#guard_msgs in
#eval report (
  [inMain #[⟨#[.print .uint8 (.literal 255), .print .int8 (.literal (-128)),
    .print .float64 (.floatLiteral 1.5), .convert 0 .int8 .float64 (.literal (-1)),
    .print .float64 (.value 0), .shift 1 .left .uint16 (.literal 1) .int8 (.literal 3),
    .print .uint16 (.value 1), .binary 2 .remainder .uint32 (.literal 7) (.literal 2),
    .print .uint32 (.value 2)], .ret #[]⟩]] ++
  [IR.Instruction.print .int8 (.literal 128), .print .uint8 (.literal (-1)),
    .print .int (.floatLiteral 1.5), .print .float64 (.literal 1), .print .float64 (.floatLiteral (1 / 0)),
    .binary 0 .remainder .float64 (.floatLiteral 1) (.floatLiteral 2),
    .binary 0 .bitAnd .float64 (.floatLiteral 1) (.floatLiteral 2),
    .shift 0 .left .float64 (.floatLiteral 1) .int (.literal 1),
    .shift 0 .left .int (.literal 1) .float64 (.floatLiteral 1),
    .convert 0 .bool .int (.boolLiteral true), .convert 0 .int8 .int (.literal 300)].map
    (fun instruction => inMain #[⟨#[instruction], .ret #[]⟩]))

-- Parameter and result types type arguments, call results, and returns.
private def boolFunction : IR.Function :=
  ⟨"g", #[⟨"b", .bool⟩], #[.bool], #[⟨#[], .ret #[(.argument 0)]⟩]⟩
private def pairFunction : IR.Function :=
  ⟨"p", #[⟨"x", .int⟩], #[.int, .bool], #[⟨#[], .ret #[.argument 0, .boolLiteral true]⟩]⟩
/--
info: ok
function 'main', block 0, instruction 0: expected bool operand
function 'g', block 0, terminator: expected bool operand
function 'g', block 0, terminator: return must have 1 operands
ok
function 'main', block 0, instruction 0: call to 'p' must define 2 results
function 'main', block 0, instruction 1: expected bool operand
function 'p', block 0, terminator: expected int operand
function 'p', block 0, terminator: return must have 2 operands
-/
#guard_msgs in
#eval report [
  inMain #[⟨#[.call #[0] "g" #[.boolLiteral true]], .condBr (.value 0) 1 1⟩, ⟨#[], .ret #[]⟩] #[boolFunction],
  inMain #[⟨#[.call #[0] "g" #[intValue]], .ret #[]⟩] #[boolFunction],
  ⟨#[mainFunction, { boolFunction with blocks := #[⟨#[], .ret #[intValue]⟩] }]⟩,
  ⟨#[mainFunction, { boolFunction with blocks := #[⟨#[], .ret #[]⟩] }]⟩,
  -- A call defines one value per result, and a return supplies one operand per result.
  inMain #[⟨#[.call #[0, 1] "p" #[intValue], .print .int (.value 0), .print .bool (.value 1),
    .call #[2, 3] "p" #[intValue]], .ret #[]⟩] #[pairFunction],
  inMain #[⟨#[.call #[0] "p" #[intValue]], .ret #[]⟩] #[pairFunction],
  inMain #[⟨#[.call #[0, 1] "p" #[intValue], .print .bool (.value 0)], .ret #[]⟩] #[pairFunction],
  ⟨#[mainFunction, { pairFunction with blocks := #[⟨#[], .ret #[.boolLiteral true, .argument 0]⟩] }]⟩,
  ⟨#[mainFunction, { pairFunction with blocks := #[⟨#[], .ret #[.argument 0]⟩] }]⟩]

-- Exercise the backend field contract for non-main void functions.
private def voidProgram : IR.Program := ⟨#[mainFunction, { mainFunction with name := "f" }]⟩
#guard verified voidProgram == "ok"
#guard
  let llvm := Backend.LLVM.emit voidProgram
  llvm.contains "define i32 @main()" && llvm.contains "ret i32 0" &&
    llvm.contains "define internal void @go_f()" && llvm.contains "ret void"

private def stringsProgram : IR.Program := ⟨#[
  { mainFunction with blocks := #[
    ⟨#[.printString "first".toUTF8], .br 1⟩,
    ⟨#[.printString "second".toUTF8, .printString "first".toUTF8], .ret #[]⟩] },
  { intFunction with blocks := #[
    ⟨#[.printString "second".toUTF8, .print .int (.argument 0)],
      .ret #[(.argument 0)]⟩] }]⟩
private def stringsLLVM := Backend.LLVM.emit stringsProgram

#guard verified stringsProgram == "ok"
-- String globals keep first-use order and are deduplicated.
#guard stringsLLVM.contains "@.str.0 = private unnamed_addr constant [6 x i8] c\"first\\00\"" &&
  stringsLLVM.contains "@.str.1 = private unnamed_addr constant [7 x i8] c\"second\\00\"" &&
  !stringsLLVM.contains "@.str.2"
-- String references are shared across blocks and functions.
#guard [0, 1].all fun index =>
  (stringsLLVM.splitOn s!"call void @goaot.print_line(ptr @.str.{index},").length == 3
-- Integer runtime needs in a later function are still declared.
#guard stringsLLVM.contains "@.int_format =" && stringsLLVM.contains "declare i32 @printf(ptr, ...)"

private def lowered (text : String) : Option IR.Program :=
  (parse (Source.ofString text) >>= Check.check >>= Lowering.lower).toOption

-- Integer literal forms are decoded in `Tests/Cases/run/integer_literal_forms.go`.

-- Lowering resolves parameter positions.
#guard match lowered
    "package main\nfunc f(z int, a int) int { return a - z }\nfunc main() { println(f(1, 2)) }\n" with
  | some program => verified program == "ok" && match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[.alloca 0 .int, .alloca 1 .int,
        .store 0 .int (.argument 0), .store 1 .int (.argument 1),
        .load 0 1 .int, .load 1 0 .int, .binary 2 .subtract .int (.value 0) (.value 1)],
        .ret #[(.value 2)]⟩] => true
    | _ => false
  | none => false

-- Interpreted strings decode every escape kind and keep multibyte source bytes.
#guard match lowered
    "package main\nfunc main() { println(\"\\x41\\u00e9\\U0001F600\\101\\\"\\\\\\t한\") }\n" with
  | some program => match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[.printString bytes], _⟩] => bytes.toList == "Aé😀A\"\\\t한".toUTF8.toList
    | _ => false
  | none => false

-- Dead source after a return emits no blocks or instructions.
#guard match lowered
    "package main\nfunc f() int { return 1; println(\"dead\"); if 1 < 2 { println(f() + f()) }; return f() }\nfunc main() {}" with
  | some program => verified program == "ok" && match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[], .ret #[(.literal 1)]⟩] => true
    | _ => false
  | none => false

-- Slots have function scope, while loaded values retain the block-local SSA rule.
/--
info: ok
ok
function 'main', block 0, instruction 0: slot 7 is not declared earlier in the entry block
function 'main', block 0, instruction 0: slot 7 is not declared earlier in the entry block
function 'main', block 0, instruction 0: slot 7 is not declared earlier in the entry block
function 'main', block 0, instruction 1: slot 7 is declared more than once
function 'main', block 1, instruction 0: slots must be allocated in the entry block
function 'main', block 0, instruction 1: slot 7 type mismatch
function 'main', block 0, instruction 1: slot 7 type mismatch
function 'main', block 0, instruction 1: expected bool operand
function 'main', block 0, instruction 2: expected int operand
function 'main', block 0, instruction 1: value 1 is not defined earlier in this block
function 'main', block 0, instruction 2: value 0 is defined more than once
function 'main', block 1, instruction 0: value 0 is not defined earlier in this block
function 'f', block 0, instruction 0: slot 7 is not declared earlier in the entry block
-/
#guard_msgs in
#eval report (
  [#[⟨#[.alloca 7 .int, .store 7 .int intValue], .br 1⟩,
      ⟨#[.load 0 7 .int, .print .int (.value 0), .store 7 .int (.literal 2)], .ret #[]⟩],
    #[⟨#[.alloca 7 .bool, comparison, .store 7 .bool boolValue, .load 1 7 .bool],
      .condBr (.value 1) 1 1⟩, ⟨#[], .ret #[]⟩],
    #[⟨#[.load 0 7 .int], .ret #[]⟩],
    #[⟨#[.store 7 .int intValue], .ret #[]⟩],
    #[⟨#[.load 0 7 .int, .alloca 7 .int], .ret #[]⟩],
    #[⟨#[.alloca 7 .int, .alloca 7 .bool], .ret #[]⟩],
    #[⟨#[], .br 1⟩, ⟨#[.alloca 7 .int], .ret #[]⟩],
    #[⟨#[.alloca 7 .int, .load 0 7 .bool], .ret #[]⟩],
    #[⟨#[.alloca 7 .int, .store 7 .bool boolValue], .ret #[]⟩],
    #[⟨#[.alloca 7 .bool, .store 7 .bool intValue], .ret #[]⟩],
    #[⟨#[.alloca 7 .int, comparison, .store 7 .int boolValue], .ret #[]⟩],
    #[⟨#[.alloca 7 .int, .store 7 .int (.value 1)], .ret #[]⟩],
    #[⟨#[.alloca 7 .int, .load 0 7 .int, definition], .ret #[]⟩],
    #[⟨#[.alloca 7 .int, .load 0 7 .int], .br 1⟩, ⟨#[.print .int (.value 0)], .ret #[]⟩]].map inMain ++
  [⟨#[{ mainFunction with blocks := #[⟨#[.alloca 7 .int], .ret #[]⟩] },
    { intFunction with blocks := #[⟨#[.load 0 7 .int], .ret #[(.value 0)]⟩] }]⟩])
#guard match lowered
    "package main\nfunc f() int { return 1; var x int; y := 1 < 2; x = 2; if y { x = 3 }; return x }; func main() {}" with
  | some program => verified program == "ok" && match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[.alloca 0 .int, .alloca 1 .bool], .ret #[(.literal 1)]⟩] => true
    | _ => false
  | none => false

-- Even syntax supplied directly to lowering must provide a type or an initializer.
#guard Id.run do
  let .ok file := parse (Source.ofString "package main\nfunc main() { var x int }")
    | return false
  let some function := file.functions[0]? | return false
  let some (Syntax.Stmt.varDeclaration name _ _) := function.body[0]? | return false
  let file := { file with functions := #[{ function with body := #[.varDeclaration name none none] }] }
  return match Check.check file with
    | .error error => error == ⟨.check, some name.span, "variable declaration requires a type or initializer"⟩
    | .ok _ => false

private def pending (terminator : Option IR.Terminator) : Lowering.PendingBlock :=
  { terminator }

private def pendingBuilder (blocks : Array Lowering.PendingBlock)
    (current : Option IR.BlockId) : Lowering.Builder :=
  { blocks, current }

-- Only entry-reachable blocks survive, including when dead blocks form a cycle or point back to live blocks.
#guard match (pendingBuilder #[pending (some (.br 3)), pending (some (.br 2)),
      pending (some (.condBr (.literal 1) 1 3)), pending (some (.ret #[]))] none).finish with
  | .ok blocks => match blocks with
    | #[⟨#[], .br 1⟩, ⟨#[], .ret #[]⟩] => true
    | _ => false
  | _ => false

#guard match (pendingBuilder #[pending (some (.br 2)), pending none,
      pending (some (.condBr (.literal 1) 3 4)), pending (some (.ret #[])),
      pending (some (.br 3))] none).finish with
  | .ok blocks => match blocks with
    | #[⟨#[], .br 1⟩, ⟨#[], .condBr _ 2 3⟩,
        ⟨#[], .ret #[]⟩, ⟨#[], .br 2⟩] => true
    | _ => false
  | _ => false

#guard match (pendingBuilder #[pending (some (.ret #[])), pending none] (some 1)).finish with
  | .ok blocks => match blocks with
    | #[⟨#[], .ret #[]⟩] => true
    | _ => false
  | _ => false

#guard [
    pendingBuilder #[pending none] (some 0),
    pendingBuilder #[pending (some (.br 4))] none].all
  fun builder => !(builder.finish).toBool

-- A branch in dead source cannot make its successor reachable from entry.
#guard match lowered
    "package main\nfunc f() int { return 1; println(f()); return 2 }; func main() {}" with
  | some program => verified program == "ok" && match program.functions[0]?.map (·.blocks) with
    | some blocks => match blocks with
      | #[⟨#[], .ret #[(.literal 1)]⟩] => true
      | _ => false
    | none => false
  | none => false

#guard [
    #[Checked.Stmt.print .int (.local 1)],
    #[Checked.Stmt.print .int (.call 1 #[])],
    #[Checked.Stmt.call 1 #[]],
    #[Checked.Stmt.callAssign #[none] 1 #[]]].all fun body =>
  let file : Checked.File := ⟨#[⟨"main", #[], #[], #[], body⟩]⟩
  match Lowering.lower file with
  | .error error => error.message == "internal error: invalid checked syntax"
  | .ok _ => false
