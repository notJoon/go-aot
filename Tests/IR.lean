import Compiler.Lowering
import Compiler.Backend.C
import Compiler.Backend.LLVM

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
#check_failure IR.Instruction.return boolValue
#check_failure IR.Instruction.ifThen intValue #[]
#check_failure IR.IntExpr.call "f" #[boolValue]
#check_failure IR.BoolExpr.less boolValue intValue

-- Both backends have the same success contract for lowered programs.
example : IR.Program → String := Backend.C.emit
example : IR.Program → String := Backend.LLVM.emit

def irMain : IO Unit := do
  let source := Source.ofString
    "package main\nfunc f(z int, a int) int { return a - z }\nfunc main() { println(f(1, 2)) }\n"
  let .ok file := parse source | throw (IO.userError "IR fixture did not parse")
  let .ok program := Lowering.lower file | throw (IO.userError "IR fixture did not lower")
  match program.functions[0]?.map (·.body) with
  | some #[.return (.subtract (.argument 1) (.argument 0))] => pure ()
  | _ => throw (IO.userError "lowering did not resolve parameter positions")
