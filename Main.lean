import GoAot

open GoAot

-- TODO: remove cc

private def compileFile (input output : String) : IO Unit := do
  let source := Source.ofString (← IO.FS.readFile input)
  let c ← match compileToC source with
    | .ok c => pure c
    | .error message => throw (IO.userError message)
  IO.FS.withTempFile fun handle path => do
    handle.putStr c
    handle.flush
    discard <| IO.Process.run {
      cmd := "cc"
      args := #["-std=c11", "-x", "c", path.toString, "-o", output]
    }

def main (args : List String) : IO Unit :=
  match args with
  | [input] => compileFile input "a.out"
  | [input, "-o", output] => compileFile input output
  | _ => throw (IO.userError "usage: goaot <input.go> [-o output]")
