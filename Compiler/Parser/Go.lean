module

public import Compiler.Lexer
public import Compiler.Syntax

public section

namespace GoAot

namespace GoParser

open Parser

private abbrev P := Parse TokenIterator

private def keyword (text : String) : P Token := fun it =>
  if h : Iterator.hasNext it then
    let token := Iterator.cur' it h
    match token.kind with
    | .keyword actual =>
      if actual == text then .ok (Iterator.next' it h) token
      else .err it (.other ("expected keyword '" ++ text ++ "'"))
    | _ => .err it (.other ("expected keyword '" ++ text ++ "'"))
  else
    .err it (.other ("expected keyword '" ++ text ++ "'"))

private def symbol (text : String) : P Token := fun it =>
  if h : Iterator.hasNext it then
    let token := Iterator.cur' it h
    match token.kind with
    | .symbol actual =>
      if actual == text then .ok (Iterator.next' it h) token
      else .err it (.other ("expected '" ++ text ++ "'"))
    | _ => .err it (.other ("expected '" ++ text ++ "'"))
  else
    .err it (.other ("expected '" ++ text ++ "'"))

private def semicolon : P Token :=
  Parser.label (Parser.satisfy (fun token => token.kind == TokenKind.semicolon))
    "expected semicolon"

private def identifier (source : Source) : P Syntax.Ident := do
  let token ← Parser.label
    (Parser.satisfy (fun token => token.kind == TokenKind.identifier))
    "expected identifier"
  match source.slice? token.span with
  | some text => return ⟨text.copy, token.span⟩
  | none => Parser.fail "invalid identifier span"

private def packageClause (source : Source) : P Syntax.Ident := do
  let _ ← keyword "package"
  let name ← identifier source
  let _ ← semicolon
  return name

private def functionDecl (source : Source) : P Syntax.FunctionDecl := do
  let first ← keyword "func"
  let name ← identifier source
  let _ ← symbol "("
  let _ ← symbol ")"
  let _ ← symbol "{"
  let last ← symbol "}"
  let _ ← semicolon
  return ⟨name, ⟨first.span.start, last.span.stop⟩⟩

private def file (source : Source) : P Syntax.File := do
  let packageName ← packageClause source
  let functions ← Parser.many (functionDecl source)
  Parser.label Parser.eof "expected function declaration or end of input"
  return ⟨packageName, functions⟩

end GoParser

private def parserError (source : Source) (tokens : Array Token) (rest : TokenIterator)
    (error : Parser.Error) : String :=
  let offset := match tokens[rest.idx]? with
    | some token => token.span.start
    | none => source.text.utf8ByteSize

  match source.position? offset with
  | some position => s!"{position.line}:{position.column}: {error}"
  | none => s!"offset {offset}: {error}"

/-- Parse the currently supported Go subset: a package clause and empty, parameterless functions. -/
def parse (source : Source) : Except String Syntax.File := do
  let tokens ← lex source
  match GoParser.file source ⟨tokens, 0⟩ with
  | .ok _ file => return file
  | .err rest error => throw (parserError source tokens rest error)

end GoAot
