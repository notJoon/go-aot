module

public import Compiler.Source

public section

namespace GoAot.Syntax

private instance : Repr String.Slice where
  reprPrec text prec := reprPrec text.copy prec

structure Ident where
  text : String.Slice
  span : Span
  deriving Repr, BEq

inductive BinaryOp where
  | add | subtract | less
  deriving Repr, BEq

inductive Expr where
  | stringLiteral (text : String) (span : Span)
  | intLiteral (text : String.Slice) (span : Span)
  | identifier (name : Ident)
  | call (callee : Ident) (arguments : Array Expr) (span : Span)
  | binary (op : BinaryOp) (left right : Expr) (span : Span)
  deriving Repr, BEq

def Expr.span : Expr → Span
  | .stringLiteral _ span | .intLiteral _ span | .call _ _ span | .binary _ _ _ span => span
  | .identifier name => name.span

inductive Stmt where
  | expr (value : Expr)
  | return (value : Expr)
  | ifThen (condition : Expr) (body : Array Stmt)
  deriving Repr, BEq

structure Parameter where
  name : Ident
  typeName : Ident
  deriving Repr, BEq

structure FunctionDecl where
  name : Ident
  parameters : Array Parameter
  resultType : Option Ident
  body : Array Stmt
  span : Span
  deriving Repr, BEq

structure File where
  packageName : Ident
  functions : Array FunctionDecl
  deriving Repr, BEq

end GoAot.Syntax
