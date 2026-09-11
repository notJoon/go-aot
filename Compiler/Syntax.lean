module

public import Compiler.Source

public section

namespace GoAot.Syntax

structure Ident where
  text : String
  span : Span
  deriving Repr, BEq

inductive Expr where
  | stringLiteral (text : String) (span : Span)
  | call (callee : Ident) (argument : Expr) (span : Span)
  deriving Repr, BEq

inductive Stmt where
  | expr (value : Expr)
  deriving Repr, BEq

structure FunctionDecl where
  name : Ident
  body : Array Stmt
  span : Span
  deriving Repr, BEq

structure File where
  packageName : Ident
  functions : Array FunctionDecl
  deriving Repr, BEq

end GoAot.Syntax
