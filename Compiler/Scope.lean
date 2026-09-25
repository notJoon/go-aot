module

public import Compiler.Checked
public import Compiler.Diagnostic
import Lean.Data.PersistentHashMap

public section

namespace GoAot

inductive SymbolKind where
  | parameter
  | local
  deriving BEq

/-- A parameter or local binding, with its local ID, type, and declaration span. -/
structure Symbol where
  kind : SymbolKind
  id : Checked.LocalId
  ty : Ty
  span : Span
  deriving BEq

/-- A lexical scope with enclosing scopes ordered from nearest to outermost. -/
structure Scope where
  -- Declarations create new scopes while earlier scopes may still be referenced.
  -- Persistent updates share unchanged nodes instead of copying a bucket array.
  private current : Lean.PersistentHashMap String Symbol := {}
  private parents : List (Lean.PersistentHashMap String Symbol) := []

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
  scope.current.find? name <|> scope.parents.findSome? (·.find? name)

/-- Returns the binding of `name` in the current scope only, ignoring enclosing scopes. -/
def Scope.findHere? (scope : Scope) (name : String) : Option Symbol :=
  scope.current.find? name

/--
Adds a binding to the current scope, allowing it to shadow an enclosing binding.
Returns a diagnostic at `symbol.span` if the current scope already declares `name`.
-/
def Scope.declare (scope : Scope) (name : String) (symbol : Symbol) :
    Except Diagnostic Scope := do
  if scope.current.contains name then
    let message := if symbol.kind == .parameter then s!"duplicate parameter '{name}'"
      else s!"duplicate declaration '{name}'"
    throw ⟨.check, some symbol.span, message⟩
  return { scope with current := scope.current.insert name symbol }

end GoAot
