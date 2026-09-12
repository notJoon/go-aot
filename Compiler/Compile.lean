module

public import Compiler.Diagnostic
import Compiler.Backend.C
import Compiler.Backend.LLVM
import Compiler.Lowering

public section

namespace GoAot

/-- Compile the supported Go subset to portable C. The system C compiler performs AOT codegen. -/
def compileToC (source : Source) : Except Diagnostic String := do
  return Backend.C.emit (← Lowering.lower (← parse source))

/-- Compile the supported Go subset to target independent textual LLVM IR. -/
def compileToLLVM (source : Source) : Except Diagnostic String := do
  return Backend.LLVM.emit (← Lowering.lower (← parse source))

end GoAot
