module

public import Compiler.Diagnostic
import Compiler.Backend.C
import Compiler.Backend.LLVM
import Compiler.Lowering
import Compiler.IR.Verify

public section

namespace GoAot

private def lowerVerified (source : Source) : Except Diagnostic IR.Program := do
  let program ← Lowering.lower (← parse source)
  match IR.verify program with
  | .ok () => return program
  | .error error => throw ⟨.ir, none, error.render⟩

/-- Compile the supported Go subset to portable C. The system C compiler performs AOT codegen. -/
def compileToC (source : Source) : Except Diagnostic String := do
  return Backend.C.emit (← lowerVerified source)

/-- Compile the supported Go subset to target independent textual LLVM IR. -/
def compileToLLVM (source : Source) : Except Diagnostic String := do
  return Backend.LLVM.emit (← lowerVerified source)

end GoAot
