import GoAot
import Compiler.Scope
import Tests.Support

open GoAot GoAot.Tests

-- A failed declaration yields the empty scope, so every lookup below fails loudly.
private def declared (scope : Scope) (name : String) (symbol : Symbol) : Scope :=
  (scope.declare name symbol).toOption.getD Scope.empty

private def outer : Scope :=
  declared (declared Scope.empty "x" ⟨.parameter, 0, .int, ⟨1, 2⟩⟩)
    "y" ⟨.parameter, 1, .int, ⟨3, 4⟩⟩

private def inner : Scope :=
  declared (declared outer.enter "x" ⟨.local, 7, .bool, ⟨10, 11⟩⟩)
    "onlyInner" ⟨.local, 42, .int, ⟨12, 21⟩⟩

-- Inner declarations shadow parameters, and lookup chooses the nearest enclosing declaration.
#guard inner.find? "x" == some ⟨.local, 7, .bool, ⟨10, 11⟩⟩
#guard inner.enter.enter.find? "x" == some ⟨.local, 7, .bool, ⟨10, 11⟩⟩
#guard inner.enter.find? "y" == some ⟨.parameter, 1, .int, ⟨3, 4⟩⟩
#guard inner.find? "onlyInner" == some ⟨.local, 42, .int, ⟨12, 21⟩⟩
#guard (inner.find? "missing").isNone

-- A completed child cannot change the enclosing scope or a sibling block.
#guard [outer, outer.enter].all fun scope =>
  scope.find? "x" == some ⟨.parameter, 0, .int, ⟨1, 2⟩⟩ && (scope.find? "onlyInner").isNone

-- Only the current scope rejects a duplicate, with a message that depends on the new binding.
/--
info: parameter in outer: check some { start := 30, stop := 31 }: duplicate parameter 'x'
local in outer: check some { start := 30, stop := 31 }: duplicate declaration 'x'
local in inner: check some { start := 30, stop := 31 }: duplicate declaration 'x'
-/
#guard_msgs in
#eval show IO Unit from do
  for (label, scope, kind) in [("parameter in outer", outer, SymbolKind.parameter),
      ("local in outer", outer, .local), ("local in inner", inner, .local)] do
    let result := match scope.declare "x" ⟨kind, 0, .int, ⟨30, 31⟩⟩ with
      | .error error => s!"{Phase.name error.phase} {repr error.span?}: {error.message}"
      | .ok _ => "ok"
    IO.println s!"{label}: {result}"

-- Source programs exercise scopes through `Tests/Cases/errors`.
