import Tests.Lexer
import Tests.Golden

def main : IO Unit := do
  lexerMain
  goldenMain
