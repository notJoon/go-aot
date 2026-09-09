module

public import Compiler.Source

public section

namespace GoAot.Syntax

structure Ident where
  text : String
  span : Span
  deriving Repr, BEq

/-- The currently supported function form is `func name() {}`. -/
structure FunctionDecl where
  name : Ident
  span : Span
  deriving Repr, BEq

structure File where
  packageName : Ident
  functions : Array FunctionDecl
  deriving Repr, BEq

end GoAot.Syntax
