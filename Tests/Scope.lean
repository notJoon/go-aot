import GoAot
import Compiler.Scope

open GoAot

-- A failed declaration yields the empty scope, so every lookup below fails loudly.
private def declared (scope : Scope) (name : String) (symbol : Symbol) : Scope :=
  (scope.declare name symbol).toOption.getD Scope.empty

private def outer : Scope :=
  declared (declared Scope.empty "x" ⟨.parameter, .argument 0, .int, ⟨1, 2⟩⟩)
    "y" ⟨.parameter, .argument 1, .int, ⟨3, 4⟩⟩

private def inner : Scope :=
  declared (declared outer.enter "x" ⟨.local, .value 7, .bool, ⟨10, 11⟩⟩)
    "onlyInner" ⟨.local, .literal 42, .int, ⟨12, 21⟩⟩

-- Inner declarations shadow parameters, and lookup chooses the nearest enclosing declaration.
#guard inner.find? "x" == some ⟨.local, .value 7, .bool, ⟨10, 11⟩⟩
#guard inner.enter.enter.find? "x" == some ⟨.local, .value 7, .bool, ⟨10, 11⟩⟩
#guard inner.enter.find? "y" == some ⟨.parameter, .argument 1, .int, ⟨3, 4⟩⟩
#guard inner.find? "onlyInner" == some ⟨.local, .literal 42, .int, ⟨12, 21⟩⟩
#guard (inner.find? "missing").isNone

-- A completed child cannot change the enclosing scope or a sibling block.
#guard [outer, outer.enter].all fun scope =>
  scope.find? "x" == some ⟨.parameter, .argument 0, .int, ⟨1, 2⟩⟩ && (scope.find? "onlyInner").isNone

#guard [(outer, SymbolKind.parameter, "duplicate parameter 'x'"),
    (outer, .local, "duplicate declaration 'x'"),
    (inner, .local, "duplicate declaration 'x'")].all fun (scope, kind, message) =>
  match scope.declare "x" ⟨kind, .literal 0, .int, ⟨30, 31⟩⟩ with
  | .error actual => actual == ⟨.lowering, some ⟨30, 31⟩, message⟩
  | .ok _ => false

-- Exercise the scope through both public compilation paths, including closed CFG paths.
#guard [("package main\nfunc f(x int, ", "x", " int) int { return x }\nfunc main() {}",
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
      "(1) }; return 2 }\nfunc main() {}", "cannot call non-function 'println'")].all
  fun (before, token, after, message) =>
    let source := Source.ofString (before ++ token ++ after)
    let expected : Diagnostic := ⟨.lowering,
      some ⟨before.utf8ByteSize, before.utf8ByteSize + token.utf8ByteSize⟩, message⟩
    [compileToC, compileToLLVM].all fun compile =>
      match compile source with
      | .error actual => actual == expected
      | .ok _ => false

#guard
  let source := Source.ofString
    "package main\nfunc f(x int, y int) int { if x < y { if y < 3 { return y } }; return x }\nfunc main() { println(f(1, 2)) }"
  (compileToC source).toBool && (compileToLLVM source).toBool
