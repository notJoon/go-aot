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

-- These terms must fail because their expression types disagree.
private def intValue : IR.IntExpr := .literal 1
private def boolValue : IR.BoolExpr := .less intValue intValue
#check_failure IR.Instruction.printInt boolValue
#check_failure IR.Instruction.return intValue
#check_failure IR.Instruction.ifThen boolValue #[]
#check_failure IR.Terminator.ret (some boolValue)
#check_failure IR.Terminator.condBr intValue 1 2
#check_failure (show IR.Block from { instructions := #[] })
#check_failure IR.IntExpr.call "f" #[boolValue]
#check_failure IR.BoolExpr.less boolValue intValue

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
    verifyRejected ⟨#[{ mainFunction with blocks := #[⟨#[], terminator⟩] }]⟩ message
  let invalidExpressions : Array (IR.IntExpr × String) := #[
    (.literal 9223372036854775808, "integer literal exceeds signed 64-bit range"),
    (.argument 0, "argument index 0 is out of range"),
    (.call "missing" #[], "unknown function 'missing'"),
    (.call "f" #[], "function 'f' expects 1 arguments"),
    (.call "main" #[], "function 'main' does not return int"),
    (.call "f" #[.argument 0], "argument index 0 is out of range"),
    (.add intValue (.subtract (.argument 0) intValue), "argument index 0 is out of range")]
  for (expression, message) in invalidExpressions do
    verifyRejected ⟨#[{ mainFunction with blocks := #[⟨#[.printInt expression], .ret none⟩] },
      intFunction]⟩ message
  verifyRejected ⟨#[{ mainFunction with blocks :=
    #[⟨#[], .ret none⟩, ⟨#[.printInt (.argument 0)], .ret none⟩] }]⟩
    "argument index 0 is out of range"
  verifyRejected ⟨#[mainFunction, { intFunction with blocks :=
    #[⟨#[], .ret (some (.argument 1))⟩] }]⟩ "argument index 1 is out of range"
  verifyRejected ⟨#[{ mainFunction with blocks :=
    #[⟨#[], .condBr (.less (.argument 0) intValue) 1 1⟩, ⟨#[], .ret none⟩] }]⟩
    "argument index 0 is out of range"
  for target in #[0, 2] do
    verifyRejected ⟨#[{ mainFunction with blocks :=
      #[⟨#[], .condBr boolValue 1 target⟩, ⟨#[], .ret none⟩] }]⟩
      (if target == 0 then "branch to entry block is not allowed"
       else "branch target 2 is out of range")
  verifyAccepted ⟨#[{ mainFunction with blocks :=
    #[⟨#[], .br 1⟩, ⟨#[], .condBr boolValue 1 1⟩,
      ⟨#[.printString (ByteArray.mk #[0, 255]), .printInt (.literal 9223372036854775807)], .ret none⟩] }]⟩
  verifyAccepted ⟨#[mainFunction,
    { intFunction with blocks := #[⟨#[], .ret (some (.call "g" #[.argument 0]))⟩] },
    { intFunction with name := "g", blocks := #[⟨#[], .ret (some (.call "f" #[.argument 0]))⟩] }]⟩
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
  checkLLVMRuntimeNeeds
  let source := Source.ofString
    "package main\nfunc f(z int, a int) int { return a - z }\nfunc main() { println(f(1, 2)) }\n"
  let .ok file := parse source | throw (IO.userError "IR fixture did not parse")
  let .ok program := Lowering.lower file | throw (IO.userError "IR fixture did not lower")
  verifyAccepted program
  match program.functions[0]?.map (·.blocks) with
  | some #[⟨#[], .ret (some (.subtract (.argument 1) (.argument 0)))⟩] => pure ()
  | _ => throw (IO.userError "lowering did not resolve parameter positions")
  let source := Source.ofString
    "package main\nfunc f() int { return 1; println(\"dead\"); if 1 < 2 { println(3) }; return 2 }\nfunc main() {}"
  let .ok file := parse source | throw (IO.userError "dead-source fixture did not parse")
  let .ok program := Lowering.lower file | throw (IO.userError "dead-source fixture did not lower")
  verifyAccepted program
  match program.functions[0]?.map (·.blocks) with
  | some #[⟨#[], .ret (some (.literal 1))⟩] => pure ()
  | _ => throw (IO.userError "dead source emitted blocks or instructions")
