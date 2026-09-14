import Tests.Lexer
import Tests.Golden
import Tests.IR
import Tests.PublicInterface
import Tests.Diagnostic
import Tests.Scope

def main : IO Unit := do
  lexerMain
  goldenMain
