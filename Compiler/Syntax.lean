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
  | add | subtract | multiply | divide | remainder
  | bitAnd | bitOr | bitXor | bitClear | shiftLeft | shiftRight
  | equal | notEqual | less | lessEqual | greater | greaterEqual
  | and | or
  deriving Repr, BEq

inductive UnaryOp where
  | negate | not | complement
  deriving Repr, BEq

/-- The Go spelling of an operator, used in diagnostics. -/
def BinaryOp.symbol : BinaryOp → String
  | .add => "+" | .subtract => "-" | .multiply => "*" | .divide => "/" | .remainder => "%"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^" | .bitClear => "&^"
  | .shiftLeft => "<<" | .shiftRight => ">>"
  | .equal => "==" | .notEqual => "!=" | .less => "<" | .lessEqual => "<="
  | .greater => ">" | .greaterEqual => ">="
  | .and => "&&" | .or => "||"

inductive Expr where
  | stringLiteral (text : String) (span : Span)
  | intLiteral (text : String.Slice) (span : Span)
  | floatLiteral (text : String.Slice) (span : Span)
  | identifier (name : Ident)
  | call (callee : Ident) (arguments : Array Expr) (span : Span)
  | binary (op : BinaryOp) (left right : Expr) (span : Span)
  | unary (op : UnaryOp) (operand : Expr) (span : Span)
  deriving Repr, BEq

def Expr.span : Expr → Span
  | .stringLiteral _ span | .intLiteral _ span | .floatLiteral _ span | .call _ _ span
  | .binary _ _ _ span
  | .unary _ _ span => span
  | .identifier name => name.span

inductive Stmt where
  /--
  Declares one local variable. An explicit `typeName` represents `var`, with an optional initializer.
  A missing `typeName` represents `:=`, whose initializer is required by the parser.
  -/
  | varDeclaration (name : Ident) (typeName : Option Ident) (initializer : Option Expr)
  /-- Assigns a value to an existing variable without introducing a binding. -/
  | assignment (name : Ident) (value : Expr)
  /--
  Binds the results of one call to two or more names, declaring with `:=` when `define` is set and
  assigning with `=` otherwise. `_` discards a result.
  -/
  | multiAssignment (names : Array Ident) (define : Bool) (value : Expr)
  | expr (value : Expr)
  | return (values : Array Expr) (span : Span)
  | ifThen (condition : Expr) (body : Array Stmt) (elseBody : Option (Array Stmt))
  | forLoop (initializer : Option Stmt) (condition : Option Expr) (post : Option Stmt)
      (body : Array Stmt)
  | break (span : Span)
  | continue (span : Span)
  deriving Repr, BEq

structure Parameter where
  name : Ident
  typeName : Ident
  deriving Repr, BEq

structure FunctionDecl where
  name : Ident
  parameters : Array Parameter
  results : Array Ident
  body : Array Stmt
  span : Span
  deriving Repr, BEq

structure File where
  packageName : Ident
  functions : Array FunctionDecl
  deriving Repr, BEq

end GoAot.Syntax
