import GoAot

open GoAot

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

private def token (kind : TokenKind) (start stop : Nat) : Token :=
  ⟨kind, ⟨start, stop⟩, false⟩

private def checkSemis (text : String) (tokens : Array Token) (positions : Array Nat) : IO Unit := do
  let .ok result := insertSemicolons (Source.ofString text) tokens
    | throw (IO.userError s!"insertion failed: {text}")
  check (result.filter (! ·.inserted) == tokens) "source tokens changed"
  check (result.filter (·.inserted) == positions.map (fun p => ⟨.semicolon, ⟨p, p⟩, true⟩))
    s!"wrong semicolons: {text}: {repr result}"


private def kinds (text : String) : Except String (Array (TokenKind × Nat × Nat)) := do
  let result ← lex (Source.ofString text)
  return result.map fun t => (t.kind, t.span.start, t.span.stop)

private def checkLex (text : String) (expected : Array (TokenKind × Nat × Nat)) : IO Unit := do
  match kinds text with
  | .error e => throw (IO.userError s!"lex failed: {text}: {e}")
  | .ok got => check (got == expected) s!"wrong tokens for {text}: {repr got}"

private def checkLexFails (text : String) : IO Unit :=
  check (kinds text |>.toOption |>.isNone) s!"accepted invalid source: {text}"

private def operatorSpellings : List String :=
  ["<<=", ">>=", "&^=", "...",
   "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "&^",
   "&&", "||", "<-", "++", "--", "==", "!=", "<=", ">=", ":=",
   "+", "-", "*", "/", "%", "&", "|", "^", "<", ">", "=", "!",
   "(", ")", "[", "]", "{", "}", ",", ".", ":", "~"]

/-- Runtime heartbeats count small allocations, so comparing input sizes detects loop allocations. -/
private def parserAllocations (p : Lex.P α) (text : String) : IO Nat := do
  let input := ⟨text, text.startPos⟩
  IO.setNumHeartbeats 0
  match p input with
  | .ok rest _ =>
    unless rest.2.IsAtEnd do throw (IO.userError "allocation probe did not consume its input")
    IO.getNumHeartbeats
  | .err _ e => throw (IO.userError s!"allocation probe failed: {e}")

private def checkConstantAllocations (label : String) (p : Lex.P α) (short long : String) : IO Unit := do
  let shortCount ← parserAllocations p short
  let longCount ← parserAllocations p long
  check (longCount == shortCount) s!"{label} allocations grow with input: {shortCount} -> {longCount}"

private def lexMain : IO Unit := do
  let chars (c : Char) (n : Nat) := String.ofList (List.replicate n c)
  let copies (s : String) (n : Nat) := String.join (List.replicate n s)
  checkConstantAllocations "whitespace" (Lex.skipWhile Lex.isSpace) (chars ' ' 8) (chars ' ' 10000)
  checkConstantAllocations "block comment" Lex.blockCommentBody
    (copies "*a" 4 ++ "*/") (copies "*a" 5000 ++ "*/")
  checkConstantAllocations "digits" (Lex.digitSeq Char.isDigit)
    (copies "1_" 4 ++ "1") (copies "1_" 5000 ++ "1")
  checkConstantAllocations "interpreted string" Lex.interpretedBody
    (copies "\\u0041" 4 ++ "\"") (copies "\\u0041" 5000 ++ "\"")
  checkConstantAllocations "raw string" Lex.rawBody
    (chars 'a' 8 ++ "`") (chars 'a' 10000 ++ "`")

  -- Spans cover the literal exactly and trivia is dropped.
  checkLex "" #[]
  checkLex "\uFEFFx" #[(.identifier, 3, 4), (.semicolon, 4, 4)]
  checkLexFails "x\uFEFF"
  checkLex "  \t\n // c \n /* a\nb */ " #[]
  checkLex "/**//*/*/x" #[(.identifier, 9, 10), (.semicolon, 10, 10)]
  checkLex "package main" #[(.keyword "package", 0, 7), (.identifier, 8, 12), (.semicolon, 12, 12)]
  checkLex "_x9 가b" #[(.identifier, 0, 3), (.identifier, 4, 8), (.semicolon, 8, 8)]
  for word in ["break", "case", "chan", "const", "continue", "default", "defer", "else",
      "fallthrough", "for", "func", "go", "goto", "if", "import", "interface", "map",
      "package", "range", "return", "select", "struct", "switch", "type", "var"] do
    let stop := word.utf8ByteSize
    checkLex (word ++ " x") #[(.keyword word, 0, stop), (.identifier, stop + 1, stop + 2),
      (.semicolon, stop + 2, stop + 2)]
    checkLex (word ++ "x") #[(.identifier, 0, stop + 1), (.semicolon, stop + 1, stop + 1)]
  checkLex "a<<=b" #[(.identifier, 0, 1), (.symbol "<<=", 1, 4), (.identifier, 4, 5), (.semicolon, 5, 5)]
  checkLex "a&^=b" #[(.identifier, 0, 1), (.symbol "&^=", 1, 4), (.identifier, 4, 5), (.semicolon, 5, 5)]
  checkLex "f(x...)" #[(.identifier, 0, 1), (.symbol "(", 1, 2), (.identifier, 2, 3),
    (.symbol "...", 3, 6), (.symbol ")", 6, 7), (.semicolon, 7, 7)]
  checkLex "a.b" #[(.identifier, 0, 1), (.symbol ".", 1, 2), (.identifier, 2, 3), (.semicolon, 3, 3)]
  checkLex "x<-y" #[(.identifier, 0, 1), (.symbol "<-", 1, 3), (.identifier, 3, 4), (.semicolon, 4, 4)]
  for spelling in operatorSpellings do
    let stop := spelling.utf8ByteSize
    let kind := TokenKind.symbol spelling
    let expected := if kind.insertsSemicolon then
      #[(kind, 0, stop), (.semicolon, stop, stop)]
    else
      #[(kind, 0, stop)]
    checkLex spelling expected

  -- Literal classification.
  for (text, kind) in [("0", TokenKind.intLiteral), ("42", .intLiteral), ("1_000", .intLiteral),
      ("0600", .intLiteral), ("0o600", .intLiteral), ("0b_1010", .intLiteral),
      ("0xBadFace", .intLiteral), ("0X_67_7a", .intLiteral),
      ("0.", .floatLiteral), (".25", .floatLiteral), ("72.40", .floatLiteral),
      ("1e9", .floatLiteral), ("1E-6", .floatLiteral), ("1_5.2e+3", .floatLiteral),
      ("0x1p-2", .floatLiteral), ("0x_1FFFp-16", .floatLiteral), ("0x.1p4", .floatLiteral),
      ("0i", .imaginaryLiteral), ("2.71828i", .imaginaryLiteral), ("1e6i", .imaginaryLiteral),
      ("0x1p-2i", .imaginaryLiteral),
      ("'a'", .runeLiteral), ("'\\n'", .runeLiteral), ("'\\''", .runeLiteral),
      ("'\\377'", .runeLiteral), ("'\\xff'", .runeLiteral), ("'\\u12e4'", .runeLiteral),
      ("'\\U0001f600'", .runeLiteral), ("'가'", .runeLiteral),
      ("\"\"", .stringLiteral), ("\"a\\\"b\\n\"", .stringLiteral), ("``", .stringLiteral),
      ("\"\\377\\xff\\u12e4\\U0001f600\"", .stringLiteral), ("`a\nb`", .stringLiteral)] do
    checkLex text #[(kind, 0, text.utf8ByteSize), (.semicolon, text.utf8ByteSize, text.utf8ByteSize)]

  -- Longest match stops before the next token.
  checkLex "1if" #[(.imaginaryLiteral, 0, 2), (.identifier, 2, 3), (.semicolon, 3, 3)]
  checkLex "1..2" #[(.floatLiteral, 0, 2), (.floatLiteral, 2, 4), (.semicolon, 4, 4)]
  checkLex "1e2p3" #[(.floatLiteral, 0, 3), (.identifier, 3, 5), (.semicolon, 5, 5)]
  checkLex "0x1p2p3" #[(.floatLiteral, 0, 5), (.identifier, 5, 7), (.semicolon, 7, 7)]
  checkLex "α١" #[(.identifier, 0, 4), (.semicolon, 4, 4)]
  checkLex "𐐀𝟘" #[(.identifier, 0, 8), (.semicolon, 8, 8)]
  checkLex "x/*\n*/y" #[(.identifier, 0, 1), (.semicolon, 3, 3),
    (.identifier, 6, 7), (.semicolon, 7, 7)]
  checkLex "`a\nb`\nx" #[(.stringLiteral, 0, 5), (.semicolon, 5, 5),
    (.identifier, 6, 7), (.semicolon, 7, 7)]
  for (text, kind) in [("08i", TokenKind.imaginaryLiteral), ("0_8i", .imaginaryLiteral),
      ("08.0", .floatLiteral), ("08e1", .floatLiteral), ("0x1.p0", .floatLiteral),
      ("0x_1p0", .floatLiteral), ("'\\uD7FF'", .runeLiteral),
      ("'\\uE000'", .runeLiteral), ("\"\\U0010FFFF\"", .stringLiteral)] do
    checkLex text #[(kind, 0, text.utf8ByteSize), (.semicolon, text.utf8ByteSize, text.utf8ByteSize)]

  checkLexFails "0x"
  checkLexFails "0b2"
  match lex (Source.ofString "0o8") with
  | .error message => check (message == "1:3: expected octal digit") s!"leaked parser error: {message}"
  | .ok _ => throw (IO.userError "accepted invalid octal literal")
  checkLexFails "1_"
  checkLexFails "0x1.5"
  checkLexFails "\"a"
  checkLexFails "\"a\nb\""
  checkLexFails "`a"
  checkLexFails "'ab'"
  checkLexFails "''"
  checkLexFails "'\\q'"
  checkLexFails "'\\x1'"
  checkLexFails "/* unterminated"
  checkLexFails "#"
  -- Malformed literals must not fall back to shorter valid tokens.
  let mut accepted := #[]
  for text in ["1e", "1e+", ".5e-", ".5_", "0x1p", "0xp1", "0x.p1", "0x_.1p0",
      "0b102", "0o78", "08", "0b1.0", "0o1e2", "1p2",
      "'\\400'", "\"\\777\"", "'\\uD800'", "\"\\U00110000\"",
      "😀", "²", "١x", "a\u0301", "x\u00a0y"] do
    if (kinds text).isOk then accepted := accepted.push text
  check accepted.isEmpty s!"accepted invalid regression inputs: {repr accepted}"
  for text in ["1__2", "0x1__2", "0b1_2", "0_8", "0x_", "0x1p_2", ".5e+"] do
    checkLexFails text
  -- Assert the failure position too: accepting '.' as an operator loses this error.
  match lex (Source.ofString ".5e+") with
  | .error message => check (message.startsWith "1:5:") s!"lost exponent error: {message}"
  | .ok _ => throw (IO.userError "accepted missing exponent")
  IO.println "Go lexer: OK"

def main : IO Unit := do
  -- Compare binary search with a linear byte-by-byte position calculation, including EOF.
  for text in ["", "a", "\n", "\n\n", "a\r\nb\rc", "가\t나\n끝\n"] do
    let source := Source.ofString text
    let bytes := text.toUTF8
    let mut line := 1
    let mut column := 1
    for offset in [:bytes.size + 1] do
      check (source.position? offset == some ⟨offset, line, column⟩) s!"position {offset}"
      if bytes[offset]? == some 10 then
        line := line + 1
        column := 1
      else column := column + 1
    check ((source.position? (bytes.size + 1)).isNone) "past EOF"

  let ident := token .identifier
  checkSemis "" #[] #[]
  checkSemis "// comment\n" #[] #[]
  checkSemis "x" #[ident 0 1] #[1]
  checkSemis "x\n\n" #[ident 0 1] #[1]
  checkSemis "x\r\ny" #[ident 0 1, ident 3 4] #[2, 4]
  checkSemis "x\ry" #[ident 0 1, ident 2 3] #[3]
  checkSemis "x;\n" #[ident 0 1, token .semicolon 1 2] #[]
  checkSemis "x // c\ny" #[ident 0 1, ident 7 8] #[6, 8]
  checkSemis "x // c" #[ident 0 1] #[6]
  checkSemis "x/*\n\n*/y" #[ident 0 1, ident 7 8] #[3, 8]
  checkSemis "x/*c*/y" #[ident 0 1, ident 6 7] #[7]
  checkSemis "x/*\n*/" #[ident 0 1] #[3]
  checkSemis "`a\nb`\ny" #[token .stringLiteral 0 5, ident 6 7] #[5, 7]
  checkSemis "(x\n)" #[token (.symbol "(") 0 1, ident 1 2, token (.symbol ")") 3 4] #[2, 4]
  checkSemis "{x}" #[token (.symbol "{") 0 1, ident 1 2, token (.symbol "}") 2 3] #[3]
  checkSemis "x,\ny" #[ident 0 1, token (.symbol ",") 1 2, ident 3 4] #[4]
  for (kind, spelling) in [(.identifier, "x"), (.intLiteral, "1"), (.floatLiteral, "1.0"),
      (.imaginaryLiteral, "1i"), (.runeLiteral, "'a'"), (.stringLiteral, "\"a\""),
      (.keyword "break", "break"), (.keyword "continue", "continue"),
      (.keyword "fallthrough", "fallthrough"), (.keyword "return", "return"),
      (.symbol "++", "++"), (.symbol "--", "--"), (.symbol ")", ")"),
      (.symbol "]", "]"), (.symbol "}", "}")] do
    checkSemis spelling #[token kind 0 spelling.utf8ByteSize] #[spelling.utf8ByteSize]
  for spelling in ["if", "for", "else", "func", "goto"] do
    checkSemis spelling #[token (.keyword spelling) 0 spelling.utf8ByteSize] #[]
  for tokens in [#[ident 1 0], #[ident 0 2], #[ident 0 1, ident 0 1]] do
    check (match insertSemicolons (Source.ofString "x") tokens with
      | .error _ => true | .ok _ => false) "invalid spans accepted"

  -- A zero-width synthetic token still commits a parser alternative.
  let it : TokenIterator := ⟨#[⟨.semicolon, ⟨0, 0⟩, true⟩], 0⟩
  let consumeFail : Parse TokenIterator Unit := do
    let _ ← Parser.any
    Parser.fail "after semicolon"
  match (consumeFail <|> pure ()) it with
  | .err rest _ => check (rest.idx == 1) "lost token progress"
  | .ok _ _ => throw (IO.userError "retried a consumed alternative")
  match (Parser.attempt consumeFail <|> pure ()) it with
  | .ok rest _ => check (rest.idx == 0) "attempt did not rewind"
  | .err _ _ => throw (IO.userError "attempt did not retry")
  IO.println "Source positions and semicolon insertion: OK"
  lexMain
