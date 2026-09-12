import GoAot

open GoAot

private def compileFile (input output backend : String) : IO Unit := do
  let source := Source.ofString (← IO.FS.readFile input)
  let (generated, compiler, language, options) ← match backend with
    | "c" => match compileToC source with
      | .ok c => pure (c, "cc", "c", #["-O2", "-std=c11"])
      | .error message => throw (IO.userError message)
    -- The Lean toolchain Clang on macOS cannot locate the host SDK during linking.
    | "llvm" => match compileToLLVM source with
      | .ok llvm => pure (llvm, if System.Platform.isOSX then "/usr/bin/clang" else "clang",
          "ir", #["-O2", "-Wno-override-module"])
      | .error message => throw (IO.userError message)
    | _ => throw (IO.userError s!"unknown backend '{backend}'")
  IO.FS.withTempFile fun handle path => do
    handle.putStr generated
    handle.flush
    discard <| IO.Process.run {
      cmd := compiler
      args := options ++ #["-x", language, path.toString, "-o", output]
    }

def main (args : List String) : IO Unit := do
  -- Keep C as the default until LLVM correctness and benchmark gates are complete.
  match args with
  | [input] => compileFile input "a.out" "c"
  | [input, "-o", output] => compileFile input output "c"
  | [input, "-o", output, "--backend", backend] => compileFile input output backend
  | _ => throw (IO.userError
      "usage: goaot <input.go> [-o output] [--backend llvm|c]")
