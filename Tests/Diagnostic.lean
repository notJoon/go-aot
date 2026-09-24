import GoAot
import Compiler.Lowering
import Compiler.Check

open GoAot

private def failsWith (result : Except Diagnostic α) (expected : Diagnostic) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

#guard ["9223372036854775808", "0x8000000000000000"].all fun literal =>
  let before := "package main\nfunc main() { println("
  let source := Source.ofString (before ++ literal ++ ") }\n")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + literal.utf8ByteSize⟩,
    "constant 9223372036854775808 overflows int"⟩
  failsWith (parse source >>= Check.check) expected &&
    failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

-- Check stage provenance survives both parser composition and public compile entry points.
#guard [("0o8", Diagnostic.mk .lexer (some ⟨2, 2⟩) "expected octal digit",
      "1:3: expected octal digit"),
    ("package 123", .mk .parser (some ⟨8, 11⟩) "expected identifier",
      "1:9: expected identifier"),
    ("package main\nfunc", .mk .parser (some ⟨17, 17⟩) "expected identifier",
      "2:5: expected identifier"),
    ("package main\n", .mk .lowering none "expected main function",
      "expected main function")].all fun (text, expected, rendered) =>
  let source := Source.ofString text
  failsWith (parse source >>= Check.check) expected &&
  failsWith (compileToC source) expected &&
  failsWith (compileToLLVM source) expected &&
  expected.render source == rendered &&
  (expected.phase != .lexer || failsWith (lex source) expected) &&
  (expected.phase == .lowering || failsWith (parse source) expected)

-- Byte offsets and columns must remain correct after a multibyte character on the same line.
private def beforeName := "package main\nfunc main() { println(\"가\"); println("
private def utf8Source := Source.ofString (beforeName ++ "missing) }\n")
private def utf8Expected : Diagnostic := ⟨.lowering,
  some ⟨beforeName.utf8ByteSize, beforeName.utf8ByteSize + 7⟩, "unknown identifier 'missing'"⟩

#guard match parse utf8Source with
  | .ok file => failsWith (Check.check file) utf8Expected
  | .error _ => false
#guard failsWith (compileToC utf8Source) utf8Expected
#guard failsWith (compileToLLVM utf8Source) utf8Expected
#guard utf8Expected.render utf8Source == "2:39: unknown identifier 'missing'"
#guard (utf8Source.slice? utf8Expected.span?.get!).map (·.copy) == some "missing"

#guard ["println()", "println(1, 2)"].all fun call =>
  let before := "package main\nfunc main() { "
  let source := Source.ofString (before ++ call ++ " }")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + call.utf8ByteSize⟩,
    "println expects one argument"⟩
  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard [("package main\nfunc f() int { return 1; println(", "); return 2 }\nfunc main() {}",
      "missing", "unknown identifier 'missing'"),
    ("package main\nfunc f() int { return 1; if 0 < 1 { println(", ") }; return 2 }\nfunc main() {}",
      "missing", "unknown identifier 'missing'"),
    ("package main\nfunc f() int { return 1; if ", " {} ; return 2 }\nfunc main() {}",
      "1", "if condition must be bool")].all fun (before, after, token, message) =>
  let source := Source.ofString (before ++ token ++ after)
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + token.utf8ByteSize⟩, message⟩
  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard
  let source := Source.ofString
    "package main\nfunc f() int { return 1; println(2) }\nfunc main() {}"
  [compileToC, compileToLLVM].all fun compile =>
    match compile source with
    | .error diagnostic =>
      diagnostic.phase == .lowering && diagnostic.message == "function 'f' must end with return"
    | .ok _ => false

#guard (Diagnostic.mk .lexer (some ⟨5, 5⟩) "invalid span").render (Source.ofString "") ==
  "offset 5: invalid span"

-- Unsupported declaration forms and malformed expressions retain the offending token's span.
#guard [
    ("var x ", "}", "", "expected variable type"),
    ("var x ", "=", " 1 }", "var declarations without an explicit type are unsupported"),
    ("a, b := 1", ",", " 2 }", "multiple variable declarations and assignments are unsupported"),
    ("x ", "+=", " 1 }", "compound assignments are unsupported"),
    ("x", "++", " }", "increment and decrement statements are unsupported"),
    ("x", "--", " }", "increment and decrement statements are unsupported"),
    ("var x int = 1", ",", " 2 }", "multiple variable declarations and assignments are unsupported"),
    ("x := 1", ",", " 2 }", "multiple variable declarations and assignments are unsupported"),
    ("x = 1", ",", " 2 }", "multiple variable declarations and assignments are unsupported"),
    ("println(1)", ",", " 2 }", "expected semicolon"),
    ("for i := 0; i < 1; a, b := f() ", "{", "} }", "for post statement cannot declare a variable"),
    ("x := ", "}", "", "expected expression"),
    ("", "f", "() = 1 }", "assignment target must be an identifier"),
    ("", "1", " = 2 }", "assignment target must be an identifier")].all
  fun (before, token, after, message) =>
    let before := "package main\nfunc main() { " ++ before
    let source := Source.ofString (before ++ token ++ after)
    let expected : Diagnostic := ⟨.parser,
      some ⟨before.utf8ByteSize, before.utf8ByteSize + token.utf8ByteSize⟩, message⟩
    failsWith (parse source) expected && failsWith (compileToC source) expected &&
      failsWith (compileToLLVM source) expected

-- Source locations distinguish an existing binding from the later offending declaration or use.
#guard [
    ("var x int; var ", "x", " int", "duplicate declaration 'x'"),
    ("x := 1; ", "x", " := 2", "duplicate declaration 'x'"),
    ("", "missing", " = 1", "unknown identifier 'missing'"),
    ("x := ", "x", "", "unknown identifier 'x'"),
    ("var x int = ", "1 < 2", "", "initializer must be int"),
    ("println(\"가\"); ", "missing", " = 1", "unknown identifier 'missing'")].all
  fun (before, token, after, message) =>
    let before := "package main\nfunc main() { " ++ before
    let source := Source.ofString (before ++ token ++ after ++ " }")
    let expected : Diagnostic := ⟨.lowering,
      some ⟨before.utf8ByteSize, before.utf8ByteSize + token.utf8ByteSize⟩, message⟩
    failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

-- Extra return values are reported at the first value beyond the declared results.
#guard
  let before := "package main\nfunc f() int { return 1, "
  let source := Source.ofString (before ++ "2 }\nfunc main() {}")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + 1⟩, "too many return values in function 'f'"⟩
  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard [
    ("break", "break outside loop"),
    ("continue", "continue outside loop")].all fun (keyword, message) =>
  let before := "package main\nfunc main() { "
  let source := Source.ofString (before ++ keyword ++ " }")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + keyword.utf8ByteSize⟩, message⟩
  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard
  let before := "package main\nfunc main() { for "
  let source := Source.ofString (before ++ "1 { println(2) } }")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + 1⟩, "for condition must be bool"⟩
  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard ["break", "continue"].all fun keyword =>
  let before := "package main\nfunc main() { for { " ++ keyword ++ " "
  let source := Source.ofString (before ++ "L } }")
  let expected : Diagnostic := ⟨.parser,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + 1⟩,
    s!"labeled {keyword} is unsupported"⟩
  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard
  let before := "package main\n"
  let function := "func f() int { for { return 1; break } }"
  let source := Source.ofString (before ++ function ++ "\nfunc main() {}")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + function.utf8ByteSize⟩,
    "function 'f' must end with return"⟩

  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard
  let before := "package main\nfunc main() { for i := 0; i < 1; i = i + 1 {}; println("
  let source := Source.ofString (before ++ "i) }")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨before.utf8ByteSize, before.utf8ByteSize + 1⟩, "unknown identifier 'i'"⟩
  failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected

#guard [
    ("for { break; var x int; ", "x", " := 1 }", "duplicate declaration 'x'"),
    ("for { continue; var x int; println(", "missing", ") }", "unknown identifier 'missing'")].all
  fun (beforeLoop, token, afterToken, message) =>
    let before := "package main\nfunc main() { " ++ beforeLoop
    let source := Source.ofString (before ++ token ++ afterToken ++ " }")
    let expected : Diagnostic := ⟨.lowering,
      some ⟨before.utf8ByteSize, before.utf8ByteSize + token.utf8ByteSize⟩, message⟩
    failsWith (compileToC source) expected && failsWith (compileToLLVM source) expected
