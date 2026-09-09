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

def main : IO Unit := do
  checkGolden "minimal"
  checkGolden "invalid"
  IO.println "Go parser golden tests: OK"
