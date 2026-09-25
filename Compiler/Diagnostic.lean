module

public import Compiler.Source

public section

namespace GoAot

/--
The phase that reported a diagnostic. `lexer`, `parser`, and `check` report errors in the source.
`lowering` and `ir` report only internal errors, because checked source always lowers to valid IR.
-/
inductive Phase where
  | lexer | parser | check | lowering | ir
  deriving Repr, BEq, Inhabited

structure Diagnostic where
  phase : Phase
  span? : Option Span
  message : String
  deriving Repr, BEq, Inhabited

/-- Render at the presentation boundary; columns are one-based UTF-8 byte columns. -/
def Diagnostic.render (diagnostic : Diagnostic) (source : Source) : String :=
  match diagnostic.span? with
  | none => diagnostic.message
  | some span =>
    match source.position? span.start with
    | some position => s!"{position.line}:{position.column}: {diagnostic.message}"
    | none => s!"offset {span.start}: {diagnostic.message}"

end GoAot
