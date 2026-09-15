module

public import Compiler.IR
public import Compiler.Diagnostic
import Std.Data.HashMap

public section

namespace GoAot

inductive SymbolKind where
  | parameter
  | local
  deriving BEq

/-- A parameter or local binding, with its storage slot, value kind, and declaration span. -/
structure Symbol where
  kind : SymbolKind
  slot : IR.SlotId
  valueKind : IR.ValueKind
  span : Span
  deriving BEq

/-- A lexical scope with enclosing scopes ordered from nearest to outermost. -/
structure Scope where
  private current : Std.HashMap String Symbol := {}
  private parents : List (Std.HashMap String Symbol) := []

/-- Returns an empty scope with no enclosing scopes. -/
def Scope.empty : Scope := {}

/--
Returns an empty child scope enclosed by `scope`.
The caller retains `scope` and discards the child when leaving the nested block.
-/
def Scope.enter (scope : Scope) : Scope :=
  { parents := scope.current :: scope.parents }

/-- Returns the nearest binding of `name`, or `none` if no enclosing scope declares it. -/
def Scope.find? (scope : Scope) (name : String) : Option Symbol :=
  scope.current[name]? <|> scope.parents.findSome? (·[name]?)

/--
Adds a binding to the current scope, allowing it to shadow an enclosing binding.
Returns a diagnostic at `symbol.span` if the current scope already declares `name`.
-/
def Scope.declare (scope : Scope) (name : String) (symbol : Symbol) :
    Except Diagnostic Scope := do
  if scope.current.contains name then
    let message := if symbol.kind == .parameter then s!"duplicate parameter '{name}'"
      else s!"duplicate declaration '{name}'"
    throw ⟨.lowering, some symbol.span, message⟩
  return { scope with current := scope.current.insert name symbol }

end GoAot
