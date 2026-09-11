import GoAot

open GoAot

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def renderFile (file : Syntax.File) : String := Id.run do
  let packageName := file.packageName
  let mut output := s!"package {packageName.text} {packageName.span.start}:{packageName.span.stop}\n"
  for function in file.functions do
    let name := function.name
    output := output ++ s!"func {name.text} {name.span.start}:{name.span.stop} " ++
      s!"{function.span.start}:{function.span.stop}\n"
  return output

private def renderParse (text : String) : String :=
  match parse (Source.ofString text) with
  | .ok file => renderFile file
  | .error message => "error " ++ message ++ "\n"

private def checkGolden (name : String) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let input ← IO.FS.readFile (path ++ ".go")
  let expected ← IO.FS.readFile (path ++ ".golden")
  let actual := renderParse input
  check (actual == expected) s!"golden mismatch: {name}\nexpected:\n{expected}actual:\n{actual}"

private def checkCompileGolden (name : String) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let input ← IO.FS.readFile (path ++ ".go")
  let expected ← IO.FS.readFile (path ++ ".c.golden")
  match compileToC (Source.ofString input) with
  | .ok actual =>
    check (actual == expected) s!"compile golden mismatch: {name}\n{actual}"
    IO.FS.withTempDir fun dir => do
      let cPath := dir / "program.c"
      let exePath := dir / "program"
      IO.FS.writeFile cPath actual
      discard <| IO.Process.run { cmd := "cc", args := #[cPath.toString, "-o", exePath.toString] }
      let output ← IO.Process.run { cmd := exePath.toString }
      check (output == "Hello, world!\n") s!"wrong native output: {repr output}"
  | .error message => throw (IO.userError s!"compile failed: {name}: {message}")

def main : IO Unit := do
  checkGolden "minimal"
  checkGolden "invalid"
  checkCompileGolden "hello"
  IO.println "Go parser and AOT tests: OK"
