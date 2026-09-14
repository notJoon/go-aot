module

public import Compiler.Source

public section

namespace GoAot

inductive Phase where
  | lexer | parser | lowering | ir | cBackend | llvmBackend
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
