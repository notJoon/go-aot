module

import GoAot

example : GoAot.Source → Except String String := GoAot.compileToC
example : GoAot.Source → Except String String := GoAot.compileToLLVM

#check_failure GoAot.lex
#check_failure GoAot.parse
#check_failure GoAot.IR.IntExpr
#check_failure GoAot.Lowering.lower
#check_failure GoAot.Backend.C.emit
#check_failure GoAot.Backend.LLVM.emit
#check_failure GoAot.Lexer.Internal.insertSemicolons
