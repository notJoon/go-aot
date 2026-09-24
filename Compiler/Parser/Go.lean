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

-- A constant message keeps failures on alternative paths from building strings.
private def tokenOf (kind : TokenKind) (message : String) : P Token := fun it =>
  if h : Iterator.hasNext it then
    let token := Iterator.cur' it h
    if token.kind == kind then .ok (Iterator.next' it h) token
    else .err it (.other message)
  else
    .err it (.other message)

private def semicolon : P Token :=
  tokenOf .semicolon "expected semicolon"

private def identifier (source : Source) : P Syntax.Ident := do
  let token ← tokenOf .identifier "expected identifier"
  match source.slice? token.span with
  | some text => return ⟨text, token.span⟩
  | none => Parser.fail "invalid identifier span"

private def packageClause (source : Source) : P Syntax.Ident := do
  let _ ← keyword "package"
  let name ← identifier source
  let _ ← semicolon
  return name

private def stringLiteral (source : Source) : P Syntax.Expr := do
  let token ← tokenOf .stringLiteral "expected string literal"
  match source.slice? token.span with
  | some text => return .stringLiteral text.copy token.span
  | none => Parser.fail "invalid string literal span"

private def intLiteral (source : Source) : P Syntax.Expr := do
  let token ← tokenOf .intLiteral "expected integer literal"
  match source.slice? token.span with
  | some text => return .intLiteral text token.span
  | none => Parser.fail "invalid integer literal span"

private def peekSymbol (text : String) : P Bool := do
  match ← Parser.peek? with
  | some { kind := .symbol actual, .. } => return actual == text
  | _ => return false

private def peekKeyword (text : String) : P Bool := do
  match ← Parser.peek? with
  | some { kind := .keyword actual, .. } => return actual == text
  | _ => return false

private def peekSemicolon : P Bool := do
  match ← Parser.peek? with
  | some { kind := .semicolon, .. } => return true
  | _ => return false

private def statementEnd : P Unit := do
  if ← peekSymbol "}" then return ()
  let _ ← semicolon
  return ()

private def rejectMultiple : P Unit := do
  if ← peekSymbol "," then
    Parser.fail "multiple variable declarations and assignments are unsupported"

private def binaryOperator? : P (Option (String × Syntax.BinaryOp × Nat)) := do
  let some { kind := .symbol text, .. } ← Parser.peek? | return none
  let op? : Option (Syntax.BinaryOp × Nat) := match text with
    | "||" => some (.or, 1)
    | "&&" => some (.and, 2)
    | "==" => some (.equal, 3)
    | "!=" => some (.notEqual, 3)
    | "<" => some (.less, 3)
    | "<=" => some (.lessEqual, 3)
    | ">" => some (.greater, 3)
    | ">=" => some (.greaterEqual, 3)
    | "+" => some (.add, 4)
    | "-" => some (.subtract, 4)
    | "*" => some (.multiply, 5)
    | "/" => some (.divide, 5)
    | "%" => some (.remainder, 5)
    | _ => none
  if op?.isNone && ["|", "^", "<<", ">>", "&", "&^"].contains text then
    Parser.fail "bitwise operators are unsupported"
  return op?.map fun (op, precedence) => (text, op, precedence)

private def rejectLabel (keyword : String) : P Unit := do
  if let some { kind := .identifier, .. } ← Parser.peek? then
    Parser.fail s!"labeled {keyword} is unsupported"

mutual
  private partial def expression (source : Source) : P Syntax.Expr :=
    binaryExpression source 1

  -- Precedence climbing over the Go spec levels. Every binary operator is left associative.
  private partial def binaryExpression (source : Source) (minimum : Nat) : P Syntax.Expr := do
    let mut left ← unaryExpression source
    repeat
      let some (text, op, precedence) ← binaryOperator? | break
      if precedence < minimum then break
      let _ ← symbol text
      let right ← binaryExpression source (precedence + 1)
      left := .binary op left right ⟨left.span.start, right.span.stop⟩
    return left

  private partial def unaryExpression (source : Source) : P Syntax.Expr := do
    let op? := match ← Parser.peek? with
      | some { kind := .symbol "-", .. } => some ("-", Syntax.UnaryOp.negate)
      | some { kind := .symbol "!", .. } => some ("!", .not)
      | _ => none
    let some (text, op) := op? | primary source
    let token ← symbol text
    let operand ← unaryExpression source
    return .unary op operand ⟨token.span.start, operand.span.stop⟩

  private partial def primary (source : Source) : P Syntax.Expr := do
    match ← Parser.peek? with
    | some { kind := .symbol "(", .. } =>
      let _ ← symbol "("
      let value ← expression source
      let _ ← symbol ")"
      return value
    | some { kind := .stringLiteral, .. } => stringLiteral source
    | some { kind := .intLiteral, .. } => intLiteral source
    | some { kind := .identifier, .. } =>
      let name ← identifier source
      unless ← peekSymbol "(" do return .identifier name
      let _ ← symbol "("
      let arguments ← argumentList source
      let last ← symbol ")"
      return .call name arguments ⟨name.span.start, last.span.stop⟩
    | _ => Parser.fail "expected expression"

  private partial def argumentList (source : Source) : P (Array Syntax.Expr) := do
    if ← peekSymbol ")" then return #[]
    let mut arguments := #[← expression source]
    while ← peekSymbol "," do
      let _ ← symbol ","
      arguments := arguments.push (← expression source)
    return arguments

  private partial def statement (source : Source) : P Syntax.Stmt := do
    match ← Parser.peek? with
    | some { kind := .keyword "return", .. } => returnStatement source
    | some { kind := .keyword "if", .. } => ifStatement source
    | some { kind := .keyword "for", .. } => forStatement source
    | some { kind := .keyword "break", .. } =>
      let token ← keyword "break"
      rejectLabel "break"
      statementEnd
      return .break token.span
    | some { kind := .keyword "continue", .. } =>
      let token ← keyword "continue"
      rejectLabel "continue"
      statementEnd
      return .continue token.span
    | some { kind := .keyword "var", .. } => do
      let result ← variableDeclaration source
      statementEnd
      return result
    | _ => do
      let result ← simpleStatement source
      statementEnd
      return result

  private partial def variableDeclaration (source : Source) : P Syntax.Stmt := do
    let _ ← keyword "var"
    let name ← identifier source
    if ← peekSymbol "=" then
      Parser.fail "var declarations without an explicit type are unsupported"
    rejectMultiple
    let typeName ← Parser.label (identifier source) "expected variable type"
    let initializer ← if ← peekSymbol "=" then
        let _ ← symbol "="
        pure (some (← expression source))
      else pure none
    rejectMultiple
    return .varDeclaration name (some typeName) initializer

  private partial def simpleStatement (source : Source) : P Syntax.Stmt := do
    let start ← fun it => .ok it it
    let value ← expression source
    if let .identifier _ := value then rejectMultiple
    match ← Parser.peek? with
    | some { kind := .symbol op, .. } =>
      if op == "++" || op == "--" then
        Parser.fail "increment and decrement statements are unsupported"
      if ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "&^="].contains op then
        Parser.fail "compound assignments are unsupported"
    | _ => pure ()
    if (← peekSymbol ":=") || (← peekSymbol "=") then
      let .identifier name := value
        | fun _ => .err start (.other "assignment target must be an identifier")
      let short ← peekSymbol ":="
      let _ ← symbol (if short then ":=" else "=")
      let initializer ← expression source
      rejectMultiple
      return if short then .varDeclaration name none (some initializer)
        else .assignment name initializer
    return .expr value

  private partial def returnStatement (source : Source) : P Syntax.Stmt := do
    let token ← keyword "return"
    let value ← if (← peekSemicolon) || (← peekSymbol "}") then pure none
      else some <$> expression source
    statementEnd
    return .return value token.span

  private partial def ifStatement (source : Source) : P Syntax.Stmt := do
    let result ← ifClause source
    statementEnd
    return result

  private partial def ifClause (source : Source) : P Syntax.Stmt := do
    let _ ← keyword "if"
    let condition ← expression source
    let (body, _) ← block source
    let elseBody ← if ← peekKeyword "else" then
        let _ ← keyword "else"
        if ← peekKeyword "if" then pure (some #[← ifClause source])
        else pure (some (← block source).1)
      else pure none
    return .ifThen condition body elseBody

  private partial def forStatement (source : Source) : P Syntax.Stmt := do
    let _ ← keyword "for"
    let (initializer, condition, post) ←
      if ← peekSymbol "{" then pure (none, none, none)
      else if ← peekSemicolon then forClause source none
      else do
        let first ← simpleStatement source
        if ← peekSemicolon then forClause source (some first)
        else match first with
          | .expr condition => pure (none, some condition, none)
          | _ => Parser.fail "expected for condition or semicolon"
    let (body, _) ← block source
    statementEnd
    return .forLoop initializer condition post body

  private partial def forClause (source : Source) (initializer : Option Syntax.Stmt) :
      P (Option Syntax.Stmt × Option Syntax.Expr × Option Syntax.Stmt) := do
    let _ ← semicolon
    let condition ← if ← peekSemicolon then pure none else some <$> expression source
    let _ ← semicolon
    let post ← if ← peekSymbol "{" then pure none else some <$> simpleStatement source
    if let some (.varDeclaration ..) := post then
      Parser.fail "for post statement cannot declare a variable"
    return (initializer, condition, post)

  private partial def block (source : Source) : P (Array Syntax.Stmt × Token) := do
    let _ ← symbol "{"
    -- Once inside a block, statement errors must propagate even when their position
    -- points back to the first token, as with an invalid assignment target.
    let mut body := #[]
    while !(← peekSymbol "}") && !(← Parser.isEof) do
      body := body.push (← statement source)
    let last ← symbol "}"
    return (body, last)
end

private def parameter (source : Source) : P Syntax.Parameter := do
  return ⟨← identifier source, ← identifier source⟩

private def parameterList (source : Source) : P (Array Syntax.Parameter) := do
  if ← peekSymbol ")" then return #[]
  let mut parameters := #[← parameter source]
  while ← peekSymbol "," do
    let _ ← symbol ","
    parameters := parameters.push (← parameter source)
  return parameters

private def functionDecl (source : Source) : P Syntax.FunctionDecl := do
  let first ← keyword "func"
  let name ← identifier source
  let _ ← symbol "("
  let parameters ← parameterList source
  let _ ← symbol ")"
  let resultType ← if ← peekSymbol "{" then pure none else some <$> identifier source
  let (body, last) ← block source
  let _ ← semicolon
  return ⟨name, parameters, resultType, body, ⟨first.span.start, last.span.stop⟩⟩

private def file (source : Source) : P Syntax.File := do
  let packageName ← packageClause source
  let functions ← Parser.many (functionDecl source)
  Parser.label Parser.eof "expected function declaration or end of input"
  return ⟨packageName, functions⟩

end GoParser

/-- Internal source-to-syntax interface. Own lexing so callers cannot supply raw tokens. -/
def parse (source : Source) : Except Diagnostic Syntax.File := do
  let tokens ← lex source
  match GoParser.file source ⟨tokens, 0⟩ with
  | .ok _ file => return file
  | .err rest error =>
    let span := match tokens[rest.idx]? with
      | some token => token.span
      | none => ⟨source.text.utf8ByteSize, source.text.utf8ByteSize⟩
    throw ⟨.parser, some span, toString error⟩

end GoAot
