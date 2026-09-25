module

public section

namespace GoAot.Toolchain

/--
The Clang that builds generated LLVM IR: `CLANG` when set, otherwise `clang`. On macOS the default
is `/usr/bin/clang`, because the Lean toolchain's Clang cannot locate the host SDK during linking.
-/
def clangCommand : IO String :=
  return (← IO.getEnv "CLANG").getD (if System.Platform.isOSX then "/usr/bin/clang" else "clang")

/-- Runs `clangCommand` with `arguments`, and throws Clang's error output if it fails. -/
def clang (arguments : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := ← clangCommand, args := arguments }
  unless result.exitCode == 0 do throw (IO.userError result.stderr)

end GoAot.Toolchain
