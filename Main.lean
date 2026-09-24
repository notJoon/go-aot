import GoAot

open GoAot

private def compileFile (input output : String) (emit : Bool) : IO Unit := do
  let source := Source.ofString (← IO.FS.readFile input)
  let generated ← match compileToLLVM source with
    | .ok llvm => pure llvm
    | .error diagnostic => throw (IO.userError (diagnostic.render source))

  if emit then
    IO.FS.writeFile output generated
    return

  IO.FS.withTempFile fun handle path => do
    handle.putStr generated
    handle.flush
    -- The Lean toolchain Clang on macOS cannot locate the host SDK during linking.
    discard <| IO.Process.run {
      cmd := if System.Platform.isOSX then "/usr/bin/clang" else "clang"
      args := #["-O2", "-Wno-override-module", "-x", "ir", path.toString, "-o", output]
    }

private def usage : IO.Error :=
  IO.userError "usage: goaot <input.go> [-o output]"

private structure Options where
  input : Option String := none
  output : String := "a.out"

private def parseArgs : List String → Options → Except IO.Error Options
  | [], options => pure options
  | "-o" :: output :: rest, options => parseArgs rest { options with output }
  | argument :: rest, options =>
    if argument.startsWith "-" || options.input.isSome then throw usage
    else parseArgs rest { options with input := some argument }

def main (args : List String) : IO Unit := do
  let options ← IO.ofExcept (parseArgs args {})
  let some input := options.input | throw usage

  -- An `.ll` output saves the generated LLVM IR instead of building a program.
  let emit := (options.output : System.FilePath).extension == some "ll"
  compileFile input options.output emit
