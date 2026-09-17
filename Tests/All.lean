import Tests.Lexer
import Tests.Golden
import Tests.IR
import Tests.PublicInterface
import Tests.Diagnostic
import Tests.Scope
import Tests.Check
import Tests.Performance

def main : IO Unit := do
  performanceMain
  lexerMain
  goldenMain
