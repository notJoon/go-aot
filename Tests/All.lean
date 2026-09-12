import Tests.Lexer
import Tests.Golden
import Tests.IR
import Tests.PublicInterface

def main : IO Unit := do
  lexerMain
  irMain
  goldenMain
