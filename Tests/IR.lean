import Compiler.Lowering
import Compiler.Backend.C
import Compiler.Backend.LLVM
import Compiler.IR.Verify

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
  let some (Syntax.Stmt.return (.call callee arguments _)) := function.body[0]? | return false
  let some (Syntax.Expr.binary .add (.identifier name) (.intLiteral text span) _) := arguments[0]?
    | return false
  return [(file.packageName, "main"), (function.name, "계산"), (parameter.name, "값"),
    (parameter.typeName, "int"), (resultType, "int"), (callee, "계산"), (name, "값")].all
      (fun (name, expected) => sourceView source name.text name.span expected) &&
    sourceView source text span "1_000" && text.toNat? == some 1000

-- Existing phase interfaces reject mixed inputs without result wrappers.
example : Source → Except Diagnostic Syntax.File := parse
example : Syntax.File → Except Diagnostic IR.Program := Lowering.lower
#check_failure fun (raw : Array Token) => parse raw
#check_failure fun (source : Source) => Lowering.lower source
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
  ⟨"f", #["x"], .int, #[⟨#[], .ret (some (.argument 0))⟩]⟩

private def accepted (program : IR.Program) : Bool :=
  (IR.verify program).toBool

private def rejected (program : IR.Program) (message : String) : Bool :=
  match IR.verify program with
  | .error error => error.message == message
  | .ok _ => false

#guard accepted ⟨#[mainFunction, intFunction]⟩
#guard [({ intFunction with name := "bad-name" }, "unsupported function name 'bad-name'"),
    ({ intFunction with name := "" }, "unsupported function name ''"),
    ({ intFunction with parameters := #["bad-name"] }, "unsupported parameter name 'bad-name'"),
    ({ intFunction with parameters := #["x", "x"] }, "duplicate parameter 'x'"),
    ({ intFunction with returnKind := .void }, "function 'f' must return int"),
    ({ intFunction with blocks := #[] }, "function must have an entry block"),
    ({ intFunction with blocks := #[⟨#[], .ret none⟩] }, "int function must return a value")].all
  fun (function, message) => rejected ⟨#[mainFunction, function]⟩ message
#guard rejected ⟨#[]⟩ "expected main function"
#guard rejected ⟨#[intFunction]⟩ "expected main function"
#guard rejected ⟨#[mainFunction, intFunction, intFunction]⟩ "duplicate function 'f'"
#guard [{ mainFunction with parameters := #["x"] }, { mainFunction with returnKind := .int }].all
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
    (.call 0 "main" #[], "function 'main' does not return int"),
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

-- Exercise the backend field contract before source syntax permits non-main void functions.
private def voidProgram : IR.Program := ⟨#[mainFunction, { mainFunction with name := "f" }]⟩
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
  (parse (Source.ofString text) >>= Lowering.lower).toOption

-- Lowering resolves parameter positions.
#guard match lowered
    "package main\nfunc f(z int, a int) int { return a - z }\nfunc main() { println(f(1, 2)) }\n" with
  | some program => accepted program && match (program.functions[0]?.map (·.blocks) : Option (Array IR.Block)) with
    | some #[⟨#[.binary 0 .subtract (.argument 1) (.argument 0)], .ret (some (.value 0))⟩] => true
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
