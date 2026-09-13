import GoAot

open GoAot

private def compileFile (input output backend : String) : IO Unit := do
  let source := Source.ofString (← IO.FS.readFile input)
  let (generated, compiler, language, options) ← match backend with
    | "c" => match compileToC source with
      | .ok c => pure (c, "cc", "c", #["-O2", "-std=c11"])
      | .error diagnostic => throw (IO.userError (diagnostic.render source))
    -- The Lean toolchain Clang on macOS cannot locate the host SDK during linking.
    | "llvm" => match compileToLLVM source with
      | .ok llvm => pure (llvm, if System.Platform.isOSX then "/usr/bin/clang" else "clang",
          "ir", #["-O2", "-Wno-override-module"])
      | .error diagnostic => throw (IO.userError (diagnostic.render source))
    | _ => throw (IO.userError s!"unknown backend '{backend}'")
  IO.FS.withTempFile fun handle path => do
    handle.putStr generated
    handle.flush
    discard <| IO.Process.run {
      cmd := compiler
      args := options ++ #["-x", language, path.toString, "-o", output]
    }

private def usage : IO.Error :=
  IO.userError "usage: goaot <input.go> [-o output] [--backend llvm|c]"

private structure Options where
  input : Option String := none
  output : String := "a.out"
  -- Keep C as the default until LLVM correctness and benchmark gates are complete.
  backend : String := "c"

private def parseArgs : List String → Options → Except IO.Error Options
  | [], options => pure options
  | "-o" :: output :: rest, options => parseArgs rest { options with output }
  | "--backend" :: backend :: rest, options => parseArgs rest { options with backend }
  | argument :: rest, options =>
    if argument.startsWith "-" || options.input.isSome then throw usage
    else parseArgs rest { options with input := some argument }

def main (args : List String) : IO Unit := do
  let options ← IO.ofExcept (parseArgs args {})
  let some input := options.input | throw usage
  compileFile input options.output options.backend
