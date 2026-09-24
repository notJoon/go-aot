import GoAot
import Compiler.Scope

open GoAot

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

#guard [(outer, SymbolKind.parameter, "duplicate parameter 'x'"),
    (outer, .local, "duplicate declaration 'x'"),
    (inner, .local, "duplicate declaration 'x'")].all fun (scope, kind, message) =>
  match scope.declare "x" ⟨kind, 0, .int, ⟨30, 31⟩⟩ with
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

-- Declarations become visible after the initializer and remain in their lexical scope.
#guard [
    ("func main() { x = 1 }", "unknown identifier 'x'"),
    ("func main() { println(x); var x int }", "unknown identifier 'x'"),
    ("func main() { x := x }", "unknown identifier 'x'"),
    ("func main() { var x int = x }", "unknown identifier 'x'"),
    ("func main() { var x int; var x int }", "duplicate declaration 'x'"),
    ("func main() { x := 1; x := 2 }", "duplicate declaration 'x'"),
    ("func f(x int) int { x := 1; return x }; func main() {}", "duplicate declaration 'x'"),
    ("func main() { if 1 < 2 { x := 1 }; println(x) }", "unknown identifier 'x'"),
    ("func main() { if 1 < 2 { x := 1 }; if 1 < 2 { println(x) } }", "unknown identifier 'x'"),
    ("func main() { var x int = 1 < 2 }", "initializer must be int"),
    ("func main() { var x int; x = 1 < 2 }", "assignment type does not match variable type"),
    ("func main() { x := 1 < 2; x = 1 }", "assignment type does not match variable type"),
    ("func main() { var x string }", "only int and bool variable types are supported"),
    ("func main() { x := \"text\" }", "expected int expression"),
    ("func main() { println := 1; println(2) }", "cannot call non-function 'println'"),
    ("func f() int { return 1 }; func main() { f := 2; x := f() }", "cannot call non-function 'f'"),
    ("func main() { _ := 1 }", "unsupported local name '_'"),
    ("func f() int { return 1; var x int; x := 2; return x }; func main() {}",
      "duplicate declaration 'x'"),
    ("func f() int { return 1; x = 2; return 0 }; func main() {}", "unknown identifier 'x'")].all
  fun (body, message) =>
    let source := Source.ofString ("package main\n" ++ body)
    [compileToC, compileToLLVM].all fun compile =>
      match compile source with
      | .error actual => actual.phase == .lowering && actual.message == message
      | .ok _ => false

#guard
  let source := Source.ofString "package main\nfunc main() { var x int; x = 1 < 2 }"
  [compileToC, compileToLLVM].all fun compile =>
    match compile source with
    | .error actual => actual.render source == "2:30: assignment type does not match variable type"
    | .ok _ => false
