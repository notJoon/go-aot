module

public import Compiler.Backend.C
public import Compiler.Backend.LLVM
public import Compiler.Lowering

public section

namespace GoAot

/-- Compile the supported Go subset to portable C. The system C compiler performs AOT codegen. -/
def compileToC (source : Source) : Except String String := do
  return Backend.C.emit (← Lowering.lower (← parse source))

/-- Compile the supported Go subset to target independent textual LLVM IR. -/
def compileToLLVM (source : Source) : Except String String := do
  Backend.LLVM.emit (← Lowering.lower (← parse source))

end GoAot
