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

structure Symbol where
  kind : SymbolKind
  operand : IR.Operand
  valueKind : IR.ValueKind
  span : Span
  deriving BEq

structure Scope where
  private current : Std.HashMap String Symbol := {}
  private parents : List (Std.HashMap String Symbol) := []

def Scope.empty : Scope := {}

-- The caller keeps its scope. Returning from a nested block discards the child.
def Scope.enter (scope : Scope) : Scope :=
  { parents := scope.current :: scope.parents }

def Scope.find? (scope : Scope) (name : String) : Option Symbol :=
  scope.current[name]? <|> scope.parents.findSome? (·[name]?)

def Scope.declare (scope : Scope) (name : String) (symbol : Symbol) :
    Except Diagnostic Scope := do
  if scope.current.contains name then
    let message := if symbol.kind == .parameter then s!"duplicate parameter '{name}'"
      else s!"duplicate declaration '{name}'"
    throw ⟨.lowering, some symbol.span, message⟩
  return { scope with current := scope.current.insert name symbol }

end GoAot
