module

import GoAot

example : GoAot.Source → Except GoAot.Diagnostic String := GoAot.compileToC
example : GoAot.Source → Except GoAot.Diagnostic String := GoAot.compileToLLVM
example : GoAot.Diagnostic → GoAot.Phase := (·.phase)
example : GoAot.Diagnostic → GoAot.Source → String := GoAot.Diagnostic.render

#check_failure GoAot.lex
#check_failure GoAot.parse
#check_failure GoAot.IR.IntExpr
#check_failure GoAot.IR.Block
#check_failure GoAot.IR.Terminator
#check_failure GoAot.Lowering.lower
#check_failure GoAot.Backend.C.emit
#check_failure GoAot.Backend.LLVM.emit
#check_failure GoAot.Lexer.Internal.insertSemicolons
