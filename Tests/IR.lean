import Compiler.Lowering
import Compiler.Check
import Compiler.Backend.C
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
  let some resultType := function.resultType | return false
  let some (Syntax.Stmt.return (some (.call callee arguments _)) _) := function.body[0]? | return false
  let some (Syntax.Expr.binary .add (.identifier name) (.intLiteral text span) _) := arguments[0]?
    | return false
  return [(file.packageName, "main"), (function.name, "계산"), (parameter.name, "값"),
    (parameter.typeName, "int"), (resultType, "int"), (callee, "계산"), (name, "값")].all
      (fun (name, expected) => sourceView source name.text name.span expected) &&
    sourceView source text span "1_000" && text.toNat? == some 1000

#guard ["a", "Z", "_", "a0", "_09", "Ab_c123"].all IR.validName
#guard ["", "0", "9abc", "a-b", "a b", "a\n", "가", "a가", "a١", "a\x00"].all
  fun name => !IR.validName name

#guard match (parse (Source.ofString
    "package main\nfunc f() int { return 1 }\nfunc f() int { return 2 }\nfunc main() {}\n")).bind Check.check with
  | .error error => error == ⟨.lowering, some ⟨44, 45⟩, "duplicate function 'f'"⟩
  | .ok _ => false

-- Existing phase interfaces reject mixed inputs without result wrappers.
example : Source → Except Diagnostic Syntax.File := parse
example : Syntax.File → Except Diagnostic Checked.File := Check.check
example : Checked.File → Except Diagnostic IR.Program := Lowering.lower
#check_failure fun (raw : Array Token) => parse raw
#check_failure fun (source : Source) => Check.check source
#check_failure fun (file : Syntax.File) => Backend.C.emit file
#check_failure fun (file : Syntax.File) => Backend.LLVM.emit file

private def intValue : IR.Operand := .literal 1
private def comparison : IR.Instruction := .binary 0 .less intValue intValue
private def boolValue : IR.Operand := .value 0
#check_failure (show IR.Block from { instructions := #[] })

-- Both backends have the same success contract for lowered programs.
example : IR.Program → String := Backend.C.emit
example : IR.Program → String := Backend.LLVM.emit
example : IR.Program → Except IR.VerifyError Unit := IR.verify

private def mainFunction : IR.Function := ⟨"main", #[], .void, #[⟨#[], .ret none⟩]⟩
private def intFunction : IR.Function :=
  ⟨"f", #[⟨"x", .int⟩], .value .int, #[⟨#[], .ret (some (.argument 0))⟩]⟩

private def accepted (program : IR.Program) : Bool :=
  (IR.verify program).toBool

private def rejected (program : IR.Program) (message : String) : Bool :=
  match IR.verify program with
  | .error error => error.message == message
  | .ok _ => false

#guard accepted ⟨#[mainFunction, intFunction]⟩
#guard [({ intFunction with name := "bad-name" }, "unsupported function name 'bad-name'"),
    ({ intFunction with name := "" }, "unsupported function name ''"),
    ({ intFunction with parameters := #[⟨"bad-name", .int⟩] }, "unsupported parameter name 'bad-name'"),
    ({ intFunction with parameters := #[⟨"x", .int⟩, ⟨"x", .int⟩] }, "duplicate parameter 'x'"),
    ({ intFunction with returnKind := .void }, "void function cannot return a value"),
    ({ intFunction with blocks := #[] }, "function must have an entry block"),
    ({ intFunction with blocks := #[⟨#[], .ret none⟩] }, "int function must return a value")].all
  fun (function, message) => rejected ⟨#[mainFunction, function]⟩ message
#guard rejected ⟨#[]⟩ "expected main function"
#guard rejected ⟨#[intFunction]⟩ "expected main function"
#guard rejected ⟨#[mainFunction, intFunction, intFunction]⟩ "duplicate function 'f'"
#guard [{ mainFunction with parameters := #[⟨"x", .int⟩] }, { mainFunction with returnKind := .value .int }].all
  fun function => rejected ⟨#[function]⟩ "main must have no parameters or return value"
#guard [(IR.Terminator.br 1, "branch target 1 is out of range"),
    (.br 0, "branch to entry block is not allowed"),
    (.condBr boolValue 1 2, "branch target 1 is out of range"),
    (.ret (some intValue), "void function cannot return a value")].all fun (terminator, message) =>
  rejected ⟨#[{ mainFunction with blocks := #[⟨#[comparison], terminator⟩] }]⟩ message
#guard [(IR.Instruction.printInt (.literal 9223372036854775808),
      "integer literal exceeds signed 64-bit range"),
    (.printInt (.argument 0), "argument index 0 is out of range"),
    (.call 0 "missing" #[], "unknown function 'missing'"),
    (.call 0 "f" #[], "function 'f' expects 1 arguments"),
    (.call 0 "main" #[], "function 'main' does not return a value"),
    (.callVoid "main" #[], "cannot call 'main'"),
    (.callVoid "f" #[intValue], "function 'f' does not return void"),
    (.call 0 "f" #[.argument 0], "argument index 0 is out of range"),
    (.binary 0 .add intValue (.argument 0), "argument index 0 is out of range")].all
  fun (instruction, message) =>
    rejected ⟨#[{ mainFunction with blocks := #[⟨#[instruction], .ret none⟩] }, intFunction]⟩ message
#guard rejected ⟨#[{ mainFunction with blocks :=
  #[⟨#[], .ret none⟩, ⟨#[.printInt (.argument 0)], .ret none⟩] }]⟩
  "argument index 0 is out of range"
#guard rejected ⟨#[mainFunction, { intFunction with blocks :=
  #[⟨#[], .ret (some (.argument 1))⟩] }]⟩ "argument index 1 is out of range"
#guard rejected ⟨#[{ mainFunction with blocks :=
  #[⟨#[.binary 0 .less (.argument 0) intValue], .condBr boolValue 1 1⟩, ⟨#[], .ret none⟩] }]⟩
  "argument index 0 is out of range"
#guard rejected ⟨#[{ mainFunction with blocks :=
  #[⟨#[comparison], .condBr boolValue 1 0⟩, ⟨#[], .ret none⟩] }]⟩
  "branch to entry block is not allowed"
#guard rejected ⟨#[{ mainFunction with blocks :=
  #[⟨#[comparison], .condBr boolValue 1 2⟩, ⟨#[], .ret none⟩] }]⟩
  "branch target 2 is out of range"
#guard accepted ⟨#[{ mainFunction with blocks :=
  #[⟨#[], .br 1⟩, ⟨#[comparison], .condBr boolValue 1 1⟩,
    ⟨#[.printString (ByteArray.mk #[0, 255]), .printInt (.literal 9223372036854775807)], .ret none⟩] }]⟩
#guard accepted ⟨#[mainFunction,
  { intFunction with blocks := #[⟨#[.call 0 "g" #[.argument 0]], .ret (some (.value 0))⟩] },
  { intFunction with name := "g", blocks := #[⟨#[.call 0 "f" #[.argument 0]], .ret (some (.value 0))⟩] }]⟩
#guard match IR.verify ⟨#[{ mainFunction with blocks :=
    #[⟨#[.printString ByteArray.empty, .printInt (.argument 0)], .ret none⟩] }]⟩ with
  | .error e => e.function? == some "main" && e.block? == some 0 && e.instruction? == some 1 && !e.terminator
  | .ok _ => false
#guard match IR.verify ⟨#[{ mainFunction with blocks := #[⟨#[], .br 0⟩] }]⟩ with
  | .error e => e.function? == some "main" && e.block? == some 0 && e.instruction? == none &&
    e.terminator && e.render ==
      "internal error: invalid IR in function 'main', block 0, terminator: branch to entry block is not allowed"
  | .ok _ => false

private def definition : IR.Instruction := .binary 0 .add intValue intValue

#guard [(#[⟨#[.printInt (.value 42)], .ret none⟩],
      "value 42 is not defined earlier in this block", 0, some 0, false),
    (#[⟨#[.printInt (.value 0), definition], .ret none⟩],
      "value 0 is not defined earlier in this block", 0, some 0, false),
    (#[⟨#[.binary 0 .add (.value 0) intValue], .ret none⟩],
      "value 0 is not defined earlier in this block", 0, some 0, false),
    (#[⟨#[definition, definition], .ret none⟩],
      "value 0 is defined more than once", 0, some 1, false),
    (#[⟨#[definition], .br 1⟩, ⟨#[definition], .ret none⟩],
      "value 0 is defined more than once", 1, some 0, false),
    (#[⟨#[definition], .br 1⟩, ⟨#[.printInt (.value 0)], .ret none⟩],
      "value 0 is not defined earlier in this block", 1, some 0, false),
    (#[⟨#[], .condBr intValue 1 1⟩, ⟨#[], .ret none⟩],
      "expected bool operand", 0, none, true),
    (#[⟨#[comparison, .binary 1 .add boolValue intValue], .ret none⟩],
      "expected int operand", 0, some 1, false),
    (#[⟨#[comparison, .call 1 "f" #[boolValue]], .ret none⟩],
      "expected int operand", 0, some 1, false),
    (#[⟨#[comparison, .printInt boolValue], .ret none⟩],
      "expected int operand", 0, some 1, false)].all
  fun ((blocks : Array IR.Block), message, block, instruction, terminator) =>
    match IR.verify ⟨#[{ mainFunction with blocks }, intFunction]⟩ with
    | .error e => e.message == message && e.function? == some "main" && e.block? == some block &&
      e.instruction? == instruction && e.terminator == terminator
    | .ok _ => false
#guard match IR.verify ⟨#[mainFunction,
    { intFunction with blocks := #[⟨#[comparison], .ret (some boolValue)⟩] }]⟩ with
  | .error e => e.message == "expected int operand" && e.function? == some "f" &&
    e.block? == some 0 && e.instruction? == none && e.terminator
  | .ok _ => false
#guard accepted ⟨#[{ mainFunction with blocks :=
  #[⟨#[.binary 100 .add intValue intValue, .binary 7 .subtract (.value 100) intValue,
    .call 42 "f" #[.value 7], .printInt (.value 42)], .ret none⟩] }, intFunction]⟩

-- Parameter and result kinds type arguments, call results, and returns.
private def boolFunction : IR.Function :=
  ⟨"g", #[⟨"b", .bool⟩], .value .bool, #[⟨#[], .ret (some (.argument 0))⟩]⟩
#guard accepted ⟨#[{ mainFunction with blocks := #[
  ⟨#[.call 0 "g" #[.boolLiteral true]], .condBr (.value 0) 1 1⟩, ⟨#[], .ret none⟩] },
  boolFunction]⟩
#guard rejected ⟨#[{ mainFunction with blocks := #[⟨#[.call 0 "g" #[intValue]], .ret none⟩] },
  boolFunction]⟩ "expected bool operand"
#guard rejected ⟨#[mainFunction, { boolFunction with blocks := #[⟨#[], .ret (some intValue)⟩] }]⟩
  "expected bool operand"
#guard rejected ⟨#[mainFunction, { boolFunction with blocks := #[⟨#[], .ret none⟩] }]⟩
  "bool function must return a value"

-- Exercise the backend field contract for non-main void functions.
private def voidProgram : IR.Program := ⟨#[mainFunction, { mainFunction with name := "f" }]⟩
#guard accepted voidProgram
#guard
  let c := Backend.C.emit voidProgram
  c.contains "int main(void)" && c.contains "return 0;" &&
    c.contains "static void go_f(void)" && c.contains "return;"
#guard
  let llvm := Backend.LLVM.emit voidProgram
  llvm.contains "define i32 @main()" && llvm.contains "ret i32 0" &&
    llvm.contains "define internal void @go_f()" && llvm.contains "ret void"

private def stringsProgram : IR.Program := ⟨#[
  { mainFunction with blocks := #[
    ⟨#[.printString "first".toUTF8], .br 1⟩,
    ⟨#[.printString "second".toUTF8, .printString "first".toUTF8], .ret none⟩] },
  { intFunction with blocks := #[
    ⟨#[.printString "second".toUTF8, .printInt (.argument 0)],
      .ret (some (.argument 0))⟩] }]⟩
private def stringsLLVM := Backend.LLVM.emit stringsProgram

#guard accepted stringsProgram
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

#guard [("010", 8), ("0_10", 8), ("0x10", 16), ("0X_67_7a", 26490),
    ("0b1", 1), ("0b_1010", 10), ("0o7", 7), ("0O7", 7),
    ("1_000", 1000), ("0x7FFFFFFFFFFFFFFF", 9223372036854775807)].all
  fun (literal, value) =>
    match lowered ("package main\nfunc main() { println(" ++ literal ++ ") }\n") with
    | some program => match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
      | some #[⟨#[.printInt (.literal actual)], .ret none⟩] => actual == value
      | _ => false
    | none => false

-- Lowering resolves parameter positions.
#guard match lowered
    "package main\nfunc f(z int, a int) int { return a - z }\nfunc main() { println(f(1, 2)) }\n" with
  | some program => accepted program && match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[.alloca 0 .int, .alloca 1 .int,
        .store 0 .int (.argument 0), .store 1 .int (.argument 1),
        .load 0 1 .int, .load 1 0 .int, .binary 2 .subtract (.value 0) (.value 1)],
        .ret (some (.value 2))⟩] => true
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
  | some program => accepted program && match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[], .ret (some (.literal 1))⟩] => true
    | _ => false
  | none => false

-- Slots have function scope, while loaded values retain the block-local SSA rule.
#guard accepted ⟨#[{ mainFunction with blocks := #[
  ⟨#[.alloca 7 .int, .store 7 .int intValue], .br 1⟩,
  ⟨#[.load 0 7 .int, .printInt (.value 0), .store 7 .int (.literal 2)], .ret none⟩] }]⟩
#guard accepted ⟨#[{ mainFunction with blocks := #[
  ⟨#[.alloca 7 .bool, comparison, .store 7 .bool boolValue, .load 1 7 .bool],
    .condBr (.value 1) 1 1⟩, ⟨#[], .ret none⟩] }]⟩
#guard [
    (#[⟨#[.load 0 7 .int], .ret none⟩], "slot 7 is not declared earlier in the entry block"),
    (#[⟨#[.store 7 .int intValue], .ret none⟩], "slot 7 is not declared earlier in the entry block"),
    (#[⟨#[.load 0 7 .int, .alloca 7 .int], .ret none⟩],
      "slot 7 is not declared earlier in the entry block"),
    (#[⟨#[.alloca 7 .int, .alloca 7 .bool], .ret none⟩], "slot 7 is declared more than once"),
    (#[⟨#[], .br 1⟩, ⟨#[.alloca 7 .int], .ret none⟩], "slots must be allocated in the entry block"),
    (#[⟨#[.alloca 7 .int, .load 0 7 .bool], .ret none⟩], "slot 7 type mismatch"),
    (#[⟨#[.alloca 7 .int, .store 7 .bool boolValue], .ret none⟩], "slot 7 type mismatch"),
    (#[⟨#[.alloca 7 .bool, .store 7 .bool intValue], .ret none⟩], "expected bool operand"),
    (#[⟨#[.alloca 7 .int, comparison, .store 7 .int boolValue], .ret none⟩], "expected int operand"),
    (#[⟨#[.alloca 7 .int, .store 7 .int (.value 1)], .ret none⟩],
      "value 1 is not defined earlier in this block"),
    (#[⟨#[.alloca 7 .int, .load 0 7 .int, definition], .ret none⟩],
      "value 0 is defined more than once"),
    (#[⟨#[.alloca 7 .int, .load 0 7 .int], .br 1⟩,
      ⟨#[.printInt (.value 0)], .ret none⟩], "value 0 is not defined earlier in this block")].all
  fun ((blocks : Array IR.Block), message) => rejected ⟨#[{ mainFunction with blocks }]⟩ message
#guard rejected ⟨#[{ mainFunction with blocks := #[⟨#[.alloca 7 .int], .ret none⟩] },
  { intFunction with blocks := #[⟨#[.load 0 7 .int], .ret (some (.value 0))⟩] }]⟩
  "slot 7 is not declared earlier in the entry block"
#guard match lowered
    "package main\nfunc f() int { return 1; var x int; y := 1 < 2; x = 2; if y { x = 3 }; return x }; func main() {}" with
  | some program => accepted program && match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[.alloca 0 .int, .alloca 1 .bool], .ret (some (.literal 1))⟩] => true
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
    | .error error => error == ⟨.lowering, some name.span, "variable declaration requires a type or initializer"⟩
    | .ok _ => false

private def pending (terminator : Option IR.Terminator) : Lowering.PendingBlock :=
  { terminator }

private def pendingBuilder (blocks : Array Lowering.PendingBlock)
    (current : Option IR.BlockId) : Lowering.Builder :=
  { blocks, current }

-- Only entry-reachable blocks survive, including when dead blocks form a cycle or point back to live blocks.
#guard match (pendingBuilder #[pending (some (.br 3)), pending (some (.br 2)),
      pending (some (.condBr (.literal 1) 1 3)), pending (some (.ret none))] none).finish with
  | .ok blocks => match blocks with
    | #[⟨#[], .br 1⟩, ⟨#[], .ret none⟩] => true
    | _ => false
  | _ => false

#guard match (pendingBuilder #[pending (some (.br 2)), pending none,
      pending (some (.condBr (.literal 1) 3 4)), pending (some (.ret none)),
      pending (some (.br 3))] none).finish with
  | .ok blocks => match blocks with
    | #[⟨#[], .br 1⟩, ⟨#[], .condBr _ 2 3⟩,
        ⟨#[], .ret none⟩, ⟨#[], .br 2⟩] => true
    | _ => false
  | _ => false

#guard match (pendingBuilder #[pending (some (.ret none)), pending none] (some 1)).finish with
  | .ok blocks => match blocks with
    | #[⟨#[], .ret none⟩] => true
    | _ => false
  | _ => false

#guard [
    pendingBuilder #[pending none] (some 0),
    pendingBuilder #[pending (some (.br 4))] none].all
  fun builder => !(builder.finish).toBool

-- A branch in dead source cannot make its successor reachable from entry.
#guard match lowered
    "package main\nfunc f() int { return 1; println(f()); return 2 }; func main() {}" with
  | some program => accepted program && match program.functions[0]?.map (·.blocks) with
    | some blocks => match blocks with
      | #[⟨#[], .ret (some (.literal 1))⟩] => true
      | _ => false
    | none => false
  | none => false

#guard [
    #[Checked.Stmt.printInt (.local 1)],
    #[Checked.Stmt.printInt (.call 1 #[])],
    #[Checked.Stmt.callVoid 1 #[]],
    #[Checked.Stmt.discard (.call 1 #[])]].all fun body =>
  let file : Checked.File := ⟨#[⟨"main", #[], #[], .void, body⟩]⟩
  match Lowering.lower file with
  | .error error => error.message == "internal error: invalid checked syntax"
  | .ok _ => false
