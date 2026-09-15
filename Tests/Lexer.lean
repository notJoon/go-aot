import Compiler.Lexer

open GoAot

private def runString (p : Parser.StringParse α) (text : String) : Option (α × String) :=
  match p ⟨text, text.startPos⟩ with
  | .ok rest value => some (value, (rest.1.sliceFrom rest.2).copy)
  | .err _ _ => none

section
open Parser

#guard runString (tried (skipStr "//")) "// c" == some (true, " c")
#guard runString (tried (skipStr "//")) "/x" == some (false, "/x")
#guard runString (tried (do skip; skipStr "y")) "ab" == some (false, "ab")
#guard runString (do skipStr "가"; offset) "가a" == some (3, "a")
#guard runString (skipStr "ab") "ac" == none
#guard runString (peekIs (· == 'a')) "" == some (false, "")
#guard runString (skipIf (· == 'a')) "ba" == some (false, "ba")
#guard runString (expect '\'' "closing '") "x" == none
#guard runString (skipWhile Char.isDigit) "12ab" == some ((), "ab")

end
private def token (kind : TokenKind) (start stop : Nat) : Token :=
  ⟨kind, ⟨start, stop⟩, false⟩

private def semis (text : String) (tokens : Array Token) (positions : Array Nat) : Bool :=
  match Lexer.Internal.insertSemicolons (Source.ofString text) tokens with
  | .ok result => result.filter (! ·.inserted) == tokens &&
    result.filter (·.inserted) == positions.map (fun p => ⟨.semicolon, ⟨p, p⟩, true⟩)
  | .error _ => false

private def kinds (text : String) : Except Diagnostic (Array (TokenKind × Nat × Nat)) := do
  let result ← lex (Source.ofString text)
  return result.map fun t => (t.kind, t.span.start, t.span.stop)

private def lexes (text : String) (expected : Array (TokenKind × Nat × Nat)) : Bool :=
  match kinds text with
  | .ok got => got == expected
  | .error _ => false

private def lexFails (text : String) : Bool :=
  !(kinds text).toBool

/-- A single token followed by its inserted semicolon. -/
private def lexesOne (text : String) (kind : TokenKind) : Bool :=
  lexes text #[(kind, 0, text.utf8ByteSize), (.semicolon, text.utf8ByteSize, text.utf8ByteSize)]

private def lexError (text : String) : Option String :=
  match lex (Source.ofString text) with
  | .error diagnostic => some (diagnostic.render (Source.ofString text))
  | .ok _ => none

private def operatorSpellings : List String :=
  ["<<=", ">>=", "&^=", "...",
   "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "&^",
   "&&", "||", "<-", "++", "--", "==", "!=", "<=", ">=", ":=",
   "+", "-", "*", "/", "%", "&", "|", "^", "<", ">", "=", "!",
   "(", ")", "[", "]", "{", "}", ",", ".", ":", "~"]

-- Compare binary search with a linear byte-by-byte position calculation, including EOF.
#guard ["", "a", "\n", "\n\n", "a\r\nb\rc", "가\t나\n끝\n"].all fun text => Id.run do
  let source := Source.ofString text
  let bytes := text.toUTF8
  let mut line := 1
  let mut column := 1
  for offset in [:bytes.size + 1] do
    unless source.position? offset == some ⟨offset, line, column⟩ do return false
    if bytes[offset]? == some 10 then
      line := line + 1
      column := 1
    else column := column + 1
  return (source.position? (bytes.size + 1)).isNone

section
private def ident := token .identifier
#guard semis "" #[] #[]
#guard semis "// comment\n" #[] #[]
#guard semis "x" #[ident 0 1] #[1]
#guard semis "x\n\n" #[ident 0 1] #[1]
#guard semis "x\r\ny" #[ident 0 1, ident 3 4] #[2, 4]
#guard semis "x\ry" #[ident 0 1, ident 2 3] #[3]
#guard semis "x;\n" #[ident 0 1, token .semicolon 1 2] #[]
#guard semis "x // c\ny" #[ident 0 1, ident 7 8] #[6, 8]
#guard semis "x // c" #[ident 0 1] #[6]
#guard semis "x/*\n\n*/y" #[ident 0 1, ident 7 8] #[3, 8]
#guard semis "x/*c*/y" #[ident 0 1, ident 6 7] #[7]
#guard semis "x/*\n*/" #[ident 0 1] #[3]
#guard semis "`a\nb`\ny" #[token .stringLiteral 0 5, ident 6 7] #[5, 7]
#guard semis "(x\n)" #[token (.symbol "(") 0 1, ident 1 2, token (.symbol ")") 3 4] #[2, 4]
#guard semis "{x}" #[token (.symbol "{") 0 1, ident 1 2, token (.symbol "}") 2 3] #[3]
#guard semis "x,\ny" #[ident 0 1, token (.symbol ",") 1 2, ident 3 4] #[4]
#guard [(TokenKind.identifier, "x"), (.intLiteral, "1"), (.floatLiteral, "1.0"),
    (.imaginaryLiteral, "1i"), (.runeLiteral, "'a'"), (.stringLiteral, "\"a\""),
    (.keyword "break", "break"), (.keyword "continue", "continue"),
    (.keyword "fallthrough", "fallthrough"), (.keyword "return", "return"),
    (.symbol "++", "++"), (.symbol "--", "--"), (.symbol ")", ")"),
    (.symbol "]", "]"), (.symbol "}", "}")].all fun (kind, spelling) =>
  semis spelling #[token kind 0 spelling.utf8ByteSize] #[spelling.utf8ByteSize]
#guard ["if", "for", "else", "func", "goto"].all fun spelling =>
  semis spelling #[token (.keyword spelling) 0 spelling.utf8ByteSize] #[]
-- Invalid spans are rejected.
#guard [#[ident 1 0], #[ident 0 2], #[ident 0 1, ident 0 1]].all fun tokens =>
  !(Lexer.Internal.insertSemicolons (Source.ofString "x") tokens).toBool
end

-- A zero-width synthetic token still commits a parser alternative.
private def semicolonIt : TokenIterator := ⟨#[⟨.semicolon, ⟨0, 0⟩, true⟩], 0⟩
private def consumeFail : Parse TokenIterator Unit := do
  let _ ← Parser.any
  Parser.fail "after semicolon"
#guard match (consumeFail <|> pure ()) semicolonIt with
  | .err rest _ => rest.idx == 1
  | .ok _ _ => false
#guard match (Parser.attempt consumeFail <|> pure ()) semicolonIt with
  | .ok rest _ => rest.idx == 0
  | .err _ _ => false

-- Spans cover the literal exactly and trivia is dropped.
#guard lexes "" #[]
#guard lexes "\uFEFFx" #[(.identifier, 3, 4), (.semicolon, 4, 4)]
#guard lexFails "x\uFEFF"
#guard lexes "  \t\n // c \n /* a\nb */ " #[]
#guard lexes "/**//*/*/x" #[(.identifier, 9, 10), (.semicolon, 10, 10)]
#guard lexes "package main" #[(.keyword "package", 0, 7), (.identifier, 8, 12), (.semicolon, 12, 12)]
#guard lexes "_x9 가b" #[(.identifier, 0, 3), (.identifier, 4, 8), (.semicolon, 8, 8)]
#guard ["break", "case", "chan", "const", "continue", "default", "defer", "else",
    "fallthrough", "for", "func", "go", "goto", "if", "import", "interface", "map",
    "package", "range", "return", "select", "struct", "switch", "type", "var"].all fun word =>
  let stop := word.utf8ByteSize
  lexes (word ++ " x") #[(.keyword word, 0, stop), (.identifier, stop + 1, stop + 2),
    (.semicolon, stop + 2, stop + 2)] &&
  lexes (word ++ "x") #[(.identifier, 0, stop + 1), (.semicolon, stop + 1, stop + 1)]
#guard lexes "a<<=b" #[(.identifier, 0, 1), (.symbol "<<=", 1, 4), (.identifier, 4, 5), (.semicolon, 5, 5)]
#guard lexes "a&^=b" #[(.identifier, 0, 1), (.symbol "&^=", 1, 4), (.identifier, 4, 5), (.semicolon, 5, 5)]
#guard lexes "f(x...)" #[(.identifier, 0, 1), (.symbol "(", 1, 2), (.identifier, 2, 3),
  (.symbol "...", 3, 6), (.symbol ")", 6, 7), (.semicolon, 7, 7)]
#guard lexes "a.b" #[(.identifier, 0, 1), (.symbol ".", 1, 2), (.identifier, 2, 3), (.semicolon, 3, 3)]
#guard lexes "x<-y" #[(.identifier, 0, 1), (.symbol "<-", 1, 3), (.identifier, 3, 4), (.semicolon, 4, 4)]
#guard operatorSpellings.all fun spelling =>
  let kind := TokenKind.symbol spelling
  if kind.insertsSemicolon then lexesOne spelling kind
  else lexes spelling #[(kind, 0, spelling.utf8ByteSize)]

-- Literal classification.
#guard [("0", TokenKind.intLiteral), ("42", .intLiteral), ("1_000", .intLiteral),
    ("0600", .intLiteral), ("0o600", .intLiteral), ("0b_1010", .intLiteral),
    ("0B1", .intLiteral), ("0O7", .intLiteral),
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
    ("\"\\377\\xff\\u12e4\\U0001f600\"", .stringLiteral), ("`a\nb`", .stringLiteral)].all
  fun (text, kind) => lexesOne text kind

-- Longest match stops before the next token.
#guard lexes "1if" #[(.imaginaryLiteral, 0, 2), (.identifier, 2, 3), (.semicolon, 3, 3)]
#guard lexes "1..2" #[(.floatLiteral, 0, 2), (.floatLiteral, 2, 4), (.semicolon, 4, 4)]
#guard lexes "1e2p3" #[(.floatLiteral, 0, 3), (.identifier, 3, 5), (.semicolon, 5, 5)]
#guard lexes "0x1p2p3" #[(.floatLiteral, 0, 5), (.identifier, 5, 7), (.semicolon, 7, 7)]
#guard lexes "α١" #[(.identifier, 0, 4), (.semicolon, 4, 4)]
#guard lexes "𐐀𝟘" #[(.identifier, 0, 8), (.semicolon, 8, 8)]
#guard lexes "x/*\n*/y" #[(.identifier, 0, 1), (.semicolon, 3, 3),
  (.identifier, 6, 7), (.semicolon, 7, 7)]
#guard lexes "`a\nb`\nx" #[(.stringLiteral, 0, 5), (.semicolon, 5, 5),
  (.identifier, 6, 7), (.semicolon, 7, 7)]
#guard [("08i", TokenKind.imaginaryLiteral), ("0_8i", .imaginaryLiteral),
    ("08.0", .floatLiteral), ("08e1", .floatLiteral), ("0x1.p0", .floatLiteral),
    ("0x_1p0", .floatLiteral), ("'\\uD7FF'", .runeLiteral),
    ("'\\uE000'", .runeLiteral), ("\"\\U0010FFFF\"", .stringLiteral)].all
  fun (text, kind) => lexesOne text kind

#guard ["0x", "0b2", "0B2", "1_", "0x1.5", "\"a", "\"a\nb\"", "`a", "'ab'", "''", "'\\q'",
  "'\\x1'", "/* unterminated", "#"].all lexFails
#guard lexError "0o8" == some "1:3: expected octal digit"
-- Malformed literals must not fall back to shorter valid tokens.
#guard ["1e", "1e+", ".5e-", ".5_", "0x1p", "0xp1", "0x.p1", "0x_.1p0",
  "0b102", "0o78", "08", "0b1.0", "0o1e2", "1p2",
  "'\\400'", "\"\\777\"", "'\\uD800'", "\"\\U00110000\"",
  "😀", "²", "١x", "a\u0301", "x\u00a0y"].all lexFails
#guard ["1__2", "0x1__2", "0b1_2", "0_8", "0x_", "0x1p_2", ".5e+"].all lexFails
-- Assert the failure position too: accepting '.' as an operator loses this error.
#guard (lexError ".5e+").any (·.startsWith "1:5:")

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
  unless longCount == shortCount do
    throw (IO.userError s!"{label} allocations grow with input: {shortCount} -> {longCount}")

-- Heartbeat counts need the compiled executable, so these stay runtime checks.
def lexerMain : IO Unit := do
  let chars (c : Char) (n : Nat) := String.ofList (List.replicate n c)
  let copies (s : String) (n : Nat) := String.join (List.replicate n s)
  checkConstantAllocations "whitespace" (Parser.skipWhile Lex.isSpace) (chars ' ' 8) (chars ' ' 10000)
  checkConstantAllocations "block comment" Lex.blockCommentBody
    (copies "*a" 4 ++ "*/") (copies "*a" 5000 ++ "*/")
  checkConstantAllocations "identifier" Lex.identifier (copies "가a1" 4) (copies "가a1" 5000)
  checkConstantAllocations "digits" (Lex.digitSeq Char.isDigit)
    (copies "1_" 4 ++ "1") (copies "1_" 5000 ++ "1")
  checkConstantAllocations "interpreted string" Lex.interpretedBody
    (copies "\\u0041" 4 ++ "\"") (copies "\\u0041" 5000 ++ "\"")
  checkConstantAllocations "raw string" Lex.rawBody
    (chars 'a' 8 ++ "`") (chars 'a' 10000 ++ "`")
  IO.println "Lexer allocations: OK"
