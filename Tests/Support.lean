import GoAot

/-!
Helpers that print test results as text, so `#guard_msgs` compares them with the expected lines
in its docstring and a failure shows a diff.
-/

open GoAot

namespace GoAot.Tests

def Phase.name : Phase → String
  | .lexer => "lexer"
  | .parser => "parser"
  | .check => "check"
  | .lowering => "lowering"
  | .ir => "ir"

/--
One line for a result: `ok`, or a diagnostic's phase, position, the source text its span covers,
and message. Example: `check 2:24 'x': unknown identifier 'x'`.
-/
def describe (source : Source) : Except Diagnostic α → String
  | .ok _ => "ok"
  | .error diagnostic =>
    let place := match diagnostic.span? with
      | none => ""
      | some span =>
        let position := match source.position? span.start with
          | some position => s!"{position.line}:{position.column}"
          | none => s!"offset {span.start}"
        let text := match source.slice? span with | some text => text.copy | none => ""
        s!" {position} '{text}'"
    s!"{Phase.name diagnostic.phase}{place}: {diagnostic.message}"

/-- `describe` for a whole compilation of `text`. -/
def describeCompile (text : String) : String :=
  let source := Source.ofString text
  describe source (compileToLLVM source)

end GoAot.Tests
