import Tests.Lexer
import Tests.IR
import Tests.PublicInterface
import Tests.Diagnostic
import Tests.Scope
import Tests.Check
import Tests.Performance
import Tests.Cases

open GoAot.Tests

/-! `#guard` checks in the imported modules run while `lake test` builds this driver. -/

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  let options ← match Options.parse args {} with
    | .ok options => pure options
    | .error message =>
      IO.eprintln message
      return 2
  let cases := #[
    ⟨"perf/budgets", "perf", true, do performanceMain; pure .pass⟩,
    ⟨"unit/lexer-allocations", "unit", true, do lexerMain; pure .pass⟩] ++
    llvmCases ++ (← fileCases options (← Gc.find))
  runCases options cases
