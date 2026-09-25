import GoAot
import Compiler.Lowering
import Compiler.Check
import Tests.Support

/-!
Diagnostics that `Tests/Cases/errors` cannot express: which phase reports an error through each
entry point, how far a span reaches, and rendering. The cases check messages and positions.
-/

open GoAot GoAot.Tests

-- Each phase's diagnostics survive every entry point that runs that phase.
/--
info: lex: lexer 1:3 '': expected octal digit
parse: lexer 1:3 '': expected octal digit
check: lexer 1:3 '': expected octal digit
compile: lexer 1:3 '': expected octal digit
parse: parser 1:9 '123': expected identifier
check: parser 1:9 '123': expected identifier
compile: parser 1:9 '123': expected identifier
parse: parser 2:5 '': expected identifier
check: parser 2:5 '': expected identifier
compile: parser 2:5 '': expected identifier
check: lowering: expected main function
compile: lowering: expected main function
-/
#guard_msgs in
#eval show IO Unit from do
  for text in ["0o8", "package 123", "package main\nfunc", "package main\n"] do
    let source := Source.ofString text
    let results := [("lex", describe source (lex source)), ("parse", describe source (parse source)),
      ("check", describe source (parse source >>= Check.check)),
      ("compile", describe source (compileToLLVM source))]
    -- An entry point that stops before the failing phase succeeds, so it is left out.
    for (entry, result) in results do
      unless result == "ok" do IO.println s!"{entry}: {result}"

-- A span covers the whole offending token or expression, not just where it starts.
/--
info: parser 2:17 '+=': compound assignments are unsupported
parser 2:16 '++': increment and decrement statements are unsupported
parser 2:28 ',': multiple variable declarations and assignments are unsupported
lowering 2:15 'println()': println expects one argument
lowering 2:27 '1 < 2': initializer must be int
lowering 2:15 'break': break outside loop
lowering 2:39 'missing': unknown identifier 'missing'
lowering 2:1 'func f() int { for { return 1; break } }': function 'f' must end with return
-/
#guard_msgs in
#eval show IO Unit from do
  for text in ["package main\nfunc main() { x += 1 }", "package main\nfunc main() { x++ }",
      "package main\nfunc main() { var x int = 1, 2 }", "package main\nfunc main() { println() }",
      "package main\nfunc main() { var x int = 1 < 2 }", "package main\nfunc main() { break }",
      "package main\nfunc main() { println(\"가\"); println(missing) }",
      "package main\nfunc f() int { for { return 1; break } }\nfunc main() {}"] do
    IO.println (describeCompile text)

#guard (Diagnostic.mk .lexer (some ⟨5, 5⟩) "invalid span").render (Source.ofString "") ==
  "offset 5: invalid span"
