import GoAot
import Compiler.Lowering

open GoAot

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def checkError (result : Except Diagnostic α) (expected : Diagnostic) : IO Unit :=
  match result with
  | .error actual => check (actual == expected) s!"wrong diagnostic: {repr actual}"
  | .ok _ => throw (IO.userError "expected diagnostic, got success")

def diagnosticMain : IO Unit := do
  -- Check stage provenance survives both parser composition and public compile entry points.
  for (text, expected, rendered) in [
      ("0o8", Diagnostic.mk .lexer (some ⟨2, 2⟩) "expected octal digit",
        "1:3: expected octal digit"),
      ("package 123", .mk .parser (some ⟨8, 11⟩) "expected identifier",
        "1:9: expected identifier"),
      ("package main\nfunc", .mk .parser (some ⟨17, 17⟩) "expected identifier",
        "2:5: expected identifier"),
      ("package main\n", .mk .lowering none "expected main function",
        "expected main function")] do
    let source := Source.ofString text
    checkError (parse source >>= Lowering.lower) expected
    checkError (compileToC source) expected
    checkError (compileToLLVM source) expected
    check (expected.render source == rendered) "wrong rendered diagnostic"
    if expected.phase == .lexer then
      checkError (lex source) expected
      checkError (parse source) expected
    else if expected.phase == .parser then
      checkError (parse source) expected

  -- Byte offsets and columns must remain correct after a multibyte character on the same line.
  let beforeName := "package main\nfunc main() { println(\"가\"); println("
  let source := Source.ofString (beforeName ++ "missing) }\n")
  let expected : Diagnostic := ⟨.lowering,
    some ⟨beforeName.utf8ByteSize, beforeName.utf8ByteSize + 7⟩, "unknown identifier 'missing'"⟩
  let .ok file := parse source | throw (IO.userError "diagnostic fixture did not parse")
  checkError (Lowering.lower file) expected
  checkError (compileToC source) expected
  checkError (compileToLLVM source) expected
  check (expected.render source == "2:39: unknown identifier 'missing'") "wrong UTF-8 column"
  check ((source.slice? expected.span?.get!).map (·.copy) == some "missing")
    "diagnostic span does not cover the identifier"

  for (before, after, token, message) in [
      ("package main\nfunc f() int { return 1; println(", "); return 2 }\nfunc main() {}",
        "missing", "unknown identifier 'missing'"),
      ("package main\nfunc f() int { return 1; if 0 < 1 { println(", ") }; return 2 }\nfunc main() {}",
        "missing", "unknown identifier 'missing'"),
      ("package main\nfunc f() int { return 1; if ", " {} ; return 2 }\nfunc main() {}",
        "1", "if condition must be bool")] do
    let source := Source.ofString (before ++ token ++ after)
    let expected : Diagnostic := ⟨.lowering,
      some ⟨before.utf8ByteSize, before.utf8ByteSize + token.utf8ByteSize⟩, message⟩
    checkError (compileToC source) expected
    checkError (compileToLLVM source) expected
  let source := Source.ofString
    "package main\nfunc f() int { return 1; println(2) }\nfunc main() {}"
  for result in [compileToC source, compileToLLVM source] do
    match result with
    | .error diagnostic =>
      check (diagnostic.phase == .lowering && diagnostic.message == "function 'f' must end with return")
        "source return rule changed"
    | .ok _ => throw (IO.userError "accepted int function without final source return")

  let outOfBounds : Diagnostic := ⟨.lexer, some ⟨5, 5⟩, "invalid span"⟩
  check (outOfBounds.render (Source.ofString "") == "offset 5: invalid span")
    "missing out-of-bounds fallback"
  IO.println "Structured diagnostics: OK"
