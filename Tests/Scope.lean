import GoAot
import Compiler.Scope

open GoAot

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def declared (scope : Scope) (name : String) (symbol : Symbol) : IO Scope :=
  match scope.declare name symbol with
  | .ok scope => pure scope
  | .error diagnostic => throw (IO.userError diagnostic.message)

def scopeMain : IO Unit := do
  let outer ← declared Scope.empty "x" ⟨.parameter, .argument 0, .int, ⟨1, 2⟩⟩
  let outer ← declared outer "y" ⟨.parameter, .argument 1, .int, ⟨3, 4⟩⟩
  let inner ← declared outer.enter "x" ⟨.local, .value 7, .bool, ⟨10, 11⟩⟩
  let inner ← declared inner "onlyInner" ⟨.local, .literal 42, .int, ⟨12, 21⟩⟩
  check (inner.find? "x" == some ⟨.local, .value 7, .bool, ⟨10, 11⟩⟩)
    "inner declaration did not shadow the parameter"
  check (inner.enter.enter.find? "x" == some ⟨.local, .value 7, .bool, ⟨10, 11⟩⟩)
    "lookup did not choose the nearest enclosing declaration"
  check (inner.enter.find? "y" == some ⟨.parameter, .argument 1, .int, ⟨3, 4⟩⟩)
    "nested lookup lost the parameter index or declaration span"
  check (inner.find? "onlyInner" == some ⟨.local, .literal 42, .int, ⟨12, 21⟩⟩)
    "local literal binding was lost"
  check ((inner.find? "missing").isNone) "unknown name resolved"

  -- A completed child cannot change the enclosing scope or a sibling block.
  for scope in [outer, outer.enter] do
    check (scope.find? "x" == some ⟨.parameter, .argument 0, .int, ⟨1, 2⟩⟩)
      "child shadow escaped its block"
    check ((scope.find? "onlyInner").isNone) "child declaration escaped its block"
  for (scope, kind, message) in [
      (outer, SymbolKind.parameter, "duplicate parameter 'x'"),
      (outer, .local, "duplicate declaration 'x'"),
      (inner, .local, "duplicate declaration 'x'")] do
    match scope.declare "x" ⟨kind, .literal 0, .int, ⟨30, 31⟩⟩ with
    | .error actual =>
      check (actual == ⟨.lowering, some ⟨30, 31⟩, message⟩) "wrong redeclaration diagnostic"
    | .ok _ => throw (IO.userError "same block redeclaration accepted")

  -- Exercise the scope through both public compilation paths, including closed CFG paths.
  for (before, token, after, message) in [
      ("package main\nfunc f(x int, ", "x", " int) int { return x }\nfunc main() {}",
        "duplicate parameter 'x'"),
      ("package main\nfunc f(x int) int { return x }\nfunc main() { println(", "x", ") }",
        "unknown identifier 'x'"),
      ("package main\nfunc f(x int) int { if x < 1 { if x < 2 { return ", "missing",
        " } }; return x }\nfunc main() {}", "unknown identifier 'missing'"),
      ("package main\nfunc f(g int) int { if g < 1 { return ", "g",
        "(1) }; return g }\nfunc main() {}", "cannot call non-function 'g'"),
      ("package main\nfunc f(println int) int { if println < 1 { ", "println",
        "(1) }; return println }\nfunc main() {}", "cannot call non-function 'println'"),
      ("package main\nfunc f(println int) int { return 1; if 0 < 1 { ", "println",
        "(1) }; return 2 }\nfunc main() {}", "cannot call non-function 'println'")] do
    let source := Source.ofString (before ++ token ++ after)
    let expected : Diagnostic := ⟨.lowering,
      some ⟨before.utf8ByteSize, before.utf8ByteSize + token.utf8ByteSize⟩, message⟩
    for compile in [compileToC, compileToLLVM] do
      match compile source with
      | .error actual => check (actual == expected) s!"wrong scope diagnostic: {repr actual}"
      | .ok _ => throw (IO.userError "invalid scoped source accepted")

  let source := Source.ofString
    "package main\nfunc f(x int, y int) int { if x < y { if y < 3 { return y } }; return x }\nfunc main() { println(f(1, 2)) }"
  for compile in [compileToC, compileToLLVM] do
    match compile source with
    | .ok _ => pure ()
    | .error diagnostic => throw (IO.userError s!"nested parameter lookup failed: {diagnostic.message}")
  IO.println "Scopes and symbol lookup: OK"
