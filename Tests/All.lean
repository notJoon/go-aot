import Tests.Lexer
import Tests.Golden
import Tests.IR
import Tests.PublicInterface
import Tests.Diagnostic

def main : IO Unit := do
  lexerMain
  irMain
  diagnosticMain
  goldenMain
