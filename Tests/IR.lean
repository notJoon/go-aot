import Compiler.Lowering
import Compiler.Backend.C
import Compiler.Backend.LLVM
import Compiler.IR.Verify

open GoAot

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

private def verifyAccepted (program : IR.Program) : IO Unit := do
  if let .error error := IR.verify program then throw (IO.userError error.render)

private def verifyRejected (program : IR.Program) (message : String) : IO Unit := do
  let .error error := IR.verify program
    | throw (IO.userError s!"IR verifier accepted invalid IR: {message}")
  unless error.message == message do
    throw (IO.userError s!"expected '{message}', got '{error.render}'")

private def verifyContracts : IO Unit := do
  verifyAccepted ⟨#[mainFunction, intFunction]⟩
  let invalidFunctions : Array (IR.Function × String) := #[
    ({ intFunction with name := "bad-name" }, "unsupported function name 'bad-name'"),
    ({ intFunction with name := "" }, "unsupported function name ''"),
    ({ intFunction with parameters := #["bad-name"] }, "unsupported parameter name 'bad-name'"),
    ({ intFunction with parameters := #["x", "x"] }, "duplicate parameter 'x'"),
    ({ intFunction with returnKind := .void }, "function 'f' must return int"),
    ({ intFunction with blocks := #[] }, "function must have an entry block"),
    ({ intFunction with blocks := #[⟨#[], .ret none⟩] }, "int function must return a value")]
  for (function, message) in invalidFunctions do
    verifyRejected ⟨#[mainFunction, function]⟩ message
  verifyRejected ⟨#[]⟩ "expected main function"
  verifyRejected ⟨#[intFunction]⟩ "expected main function"
  verifyRejected ⟨#[mainFunction, intFunction, intFunction]⟩ "duplicate function 'f'"
  for function in #[{ mainFunction with parameters := #["x"] },
      { mainFunction with returnKind := .int }] do
    verifyRejected ⟨#[function]⟩ "main must have no parameters or return value"
  let invalidTerminators : Array (IR.Terminator × String) := #[
    (.br 1, "branch target 1 is out of range"),
    (.br 0, "branch to entry block is not allowed"),
    (.condBr boolValue 1 2, "branch target 1 is out of range"),
    (.ret (some intValue), "void function cannot return a value")]
  for (terminator, message) in invalidTerminators do
    verifyRejected ⟨#[{ mainFunction with blocks := #[⟨#[comparison], terminator⟩] }]⟩ message
  let invalidInstructions : Array (IR.Instruction × String) := #[
    (.printInt (.literal 9223372036854775808), "integer literal exceeds signed 64-bit range"),
    (.printInt (.argument 0), "argument index 0 is out of range"),
    (.call 0 "missing" #[], "unknown function 'missing'"),
    (.call 0 "f" #[], "function 'f' expects 1 arguments"),
    (.call 0 "main" #[], "function 'main' does not return int"),
    (.call 0 "f" #[.argument 0], "argument index 0 is out of range"),
    (.binary 0 .add intValue (.argument 0), "argument index 0 is out of range")]
  for (instruction, message) in invalidInstructions do
    verifyRejected ⟨#[{ mainFunction with blocks := #[⟨#[instruction], .ret none⟩] },
      intFunction]⟩ message
  verifyRejected ⟨#[{ mainFunction with blocks :=
    #[⟨#[], .ret none⟩, ⟨#[.printInt (.argument 0)], .ret none⟩] }]⟩
    "argument index 0 is out of range"
  verifyRejected ⟨#[mainFunction, { intFunction with blocks :=
    #[⟨#[], .ret (some (.argument 1))⟩] }]⟩ "argument index 1 is out of range"
  verifyRejected ⟨#[{ mainFunction with blocks :=
    #[⟨#[.binary 0 .less (.argument 0) intValue], .condBr boolValue 1 1⟩, ⟨#[], .ret none⟩] }]⟩
    "argument index 0 is out of range"
  for target in #[0, 2] do
    verifyRejected ⟨#[{ mainFunction with blocks :=
      #[⟨#[comparison], .condBr boolValue 1 target⟩, ⟨#[], .ret none⟩] }]⟩
      (if target == 0 then "branch to entry block is not allowed"
       else "branch target 2 is out of range")
  verifyAccepted ⟨#[{ mainFunction with blocks :=
    #[⟨#[], .br 1⟩, ⟨#[comparison], .condBr boolValue 1 1⟩,
      ⟨#[.printString (ByteArray.mk #[0, 255]), .printInt (.literal 9223372036854775807)], .ret none⟩] }]⟩
  verifyAccepted ⟨#[mainFunction,
    { intFunction with blocks := #[⟨#[.call 0 "g" #[.argument 0]], .ret (some (.value 0))⟩] },
    { intFunction with name := "g", blocks := #[⟨#[.call 0 "f" #[.argument 0]], .ret (some (.value 0))⟩] }]⟩
  let .error instructionError := IR.verify ⟨#[{ mainFunction with blocks :=
      #[⟨#[.printString ByteArray.empty, .printInt (.argument 0)], .ret none⟩] }]⟩
    | throw (IO.userError "expected instruction error")
  unless instructionError.function? == some "main" && instructionError.block? == some 0 &&
      instructionError.instruction? == some 1 && !instructionError.terminator do
    throw (IO.userError "incorrect instruction error location")
  let .error terminatorError := IR.verify ⟨#[{ mainFunction with blocks := #[⟨#[], .br 0⟩] }]⟩
    | throw (IO.userError "expected terminator error")
  unless terminatorError.function? == some "main" && terminatorError.block? == some 0 &&
      terminatorError.instruction? == none && terminatorError.terminator &&
      terminatorError.render == "internal error: invalid IR in function 'main', block 0, terminator: branch to entry block is not allowed" do
    throw (IO.userError "incorrect terminator error location")

private def verifyValues : IO Unit := do
  let definition : IR.Instruction := .binary 0 .add intValue intValue
  let cases : Array (Array IR.Block × String × Nat × Option Nat × Bool) := #[
    (#[⟨#[.printInt (.value 42)], .ret none⟩],
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
      "expected int operand", 0, some 1, false)]
  for (blocks, message, block, instruction, terminator) in cases do
    let .error error := IR.verify ⟨#[{ mainFunction with blocks }, intFunction]⟩
      | throw (IO.userError s!"value verifier accepted: {message}")
    unless error.message == message && error.function? == some "main" &&
        error.block? == some block && error.instruction? == instruction && error.terminator == terminator do
      throw (IO.userError s!"incorrect value error: {error.render}")
  let .error error := IR.verify ⟨#[mainFunction,
      { intFunction with blocks := #[⟨#[comparison], .ret (some boolValue)⟩] }]⟩
    | throw (IO.userError "value verifier accepted bool return")
  unless error.message == "expected int operand" && error.function? == some "f" &&
      error.block? == some 0 && error.instruction? == none && error.terminator do
    throw (IO.userError s!"incorrect return kind error: {error.render}")
  verifyAccepted ⟨#[{ mainFunction with blocks :=
    #[⟨#[.binary 100 .add intValue intValue, .binary 7 .subtract (.value 100) intValue,
      .call 42 "f" #[.value 7], .printInt (.value 42)], .ret none⟩] }, intFunction]⟩

private def checkReturnKinds : IO Unit := do
  -- Exercise the backend field contract before source syntax permits non-main void functions.
  let program : IR.Program := ⟨#[mainFunction,
    { mainFunction with name := "f" }]⟩
  let c := Backend.C.emit program
  let llvm := Backend.LLVM.emit program
  unless c.contains "int main(void)" && c.contains "return 0;" &&
      c.contains "static void go_f(void)" && c.contains "return;" &&
      llvm.contains "define i32 @main()" && llvm.contains "ret i32 0" &&
      llvm.contains "define internal void @go_f()" && llvm.contains "ret void" do
    throw (IO.userError "backends ignored return kinds or changed the main ABI")

private def checkLLVMRuntimeNeeds : IO Unit := do
  let program : IR.Program := ⟨#[
    { mainFunction with blocks := #[
      ⟨#[.printString "first".toUTF8], .br 1⟩,
      ⟨#[.printString "second".toUTF8, .printString "first".toUTF8], .ret none⟩] },
    { intFunction with blocks := #[
      ⟨#[.printString "second".toUTF8, .printInt (.argument 0)],
        .ret (some (.argument 0))⟩] }]⟩
  verifyAccepted program
  let output := Backend.LLVM.emit program
  unless output.contains "@.str.0 = private unnamed_addr constant [6 x i8] c\"first\\00\"" &&
      output.contains "@.str.1 = private unnamed_addr constant [7 x i8] c\"second\\00\"" &&
      !output.contains "@.str.2" do
    throw (IO.userError "LLVM string globals lost first-use order or deduplication")
  for index in [0, 1] do
    unless (output.splitOn s!"call void @goaot.print_line(ptr @.str.{index},").length == 3 do
      throw (IO.userError "LLVM string references differ across blocks or functions")
  unless output.contains "@.int_format =" && output.contains "declare i32 @printf(ptr, ...)" do
    throw (IO.userError "LLVM missed integer runtime needs in a later function")

def irMain : IO Unit := do
  verifyContracts
  verifyValues
  checkReturnKinds
  checkLLVMRuntimeNeeds
  let source := Source.ofString
    "package main\nfunc f(z int, a int) int { return a - z }\nfunc main() { println(f(1, 2)) }\n"
  let .ok file := parse source | throw (IO.userError "IR fixture did not parse")
  let .ok program := Lowering.lower file | throw (IO.userError "IR fixture did not lower")
  verifyAccepted program
  match program.functions[0]?.map (·.blocks) with
  | some #[⟨#[.binary 0 .subtract (.argument 1) (.argument 0)], .ret (some (.value 0))⟩] => pure ()
  | _ => throw (IO.userError "lowering did not resolve parameter positions")
  let source := Source.ofString
    "package main\nfunc f() int { return 1; println(\"dead\"); if 1 < 2 { println(f() + f()) }; return f() }\nfunc main() {}"
  let .ok file := parse source | throw (IO.userError "dead-source fixture did not parse")
  let .ok program := Lowering.lower file | throw (IO.userError "dead-source fixture did not lower")
  verifyAccepted program
  match program.functions[0]?.map (·.blocks) with
  | some #[⟨#[], .ret (some (.literal 1))⟩] => pure ()
  | _ => throw (IO.userError "dead source emitted blocks or instructions")
