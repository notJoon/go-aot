module

public import Compiler.Source
public import Compiler.Parser.Parser
public import Compiler.Parser.String
import Compiler.Unicode

public section

namespace GoAot

inductive TokenKind where
  | identifier
  | intLiteral | floatLiteral | imaginaryLiteral | runeLiteral | stringLiteral
  | keyword (text : String)
  | symbol (text : String)
  | semicolon
  deriving Repr, BEq, DecidableEq, Inhabited

def TokenKind.insertsSemicolon : TokenKind → Bool
  | .identifier | .intLiteral | .floatLiteral | .imaginaryLiteral
  | .runeLiteral | .stringLiteral => true
  | .keyword s => ["break", "continue", "fallthrough", "return"].contains s
  | .symbol s => ["++", "--", ")", "]", "}"].contains s
  | .semicolon => false

structure Token where
  kind : TokenKind
  span : Span
  /-- Inserted semicolons have an empty span at the triggering newline or EOF. -/
  inserted : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/--
Insert Go semicolons into lexer output. Input contains only significant tokens, in source order,
with original byte spans; whitespace and comments are omitted and EOF is represented by array end.
The caller must already have validated tokens and comments. Gaps may contain only trivia.
Keep raw string spans intact, including their internal newlines.

This implements lexical insertion only. Omission before `)` and `}` belongs to the grammar parser.
-/
def insertSemicolons (source : Source) (tokens : Array Token) : Except String (Array Token) := do
  let sourceSize := source.text.utf8ByteSize
  let mut result := #[]
  let mut stop := 0
  let mut insertSemi := false
  for token in tokens do
    if token.span.start < stop || token.span.stop <= token.span.start ||
        token.span.stop > sourceSize || token.inserted then
      throw "expected ordered, nonempty source token spans within the source"
    if insertSemi then
      if let some nl := source.firstNewline? stop token.span.start then
        result := result.push ⟨.semicolon, ⟨nl, nl⟩, true⟩
    result := result.push token
    stop := token.span.stop
    insertSemi := token.kind.insertsSemicolon
  if insertSemi then
    let pos := (source.firstNewline? stop sourceSize).getD sourceSize
    result := result.push ⟨.semicolon, ⟨pos, pos⟩, true⟩
  return result

/-- Parser progress is measured in tokens, independently of synthetic tokens' source spans. -/
structure TokenIterator where
  tokens : Array Token
  idx : Nat := 0

instance : Parser.Iterator TokenIterator Token Nat where
  pos it := it.idx
  next it := { it with idx := it.idx + 1 }
  cur it := it.tokens[it.idx]!
  hasNext it := it.idx < it.tokens.size
  next' it _ := { it with idx := it.idx + 1 }
  cur' it h := it.tokens[it.idx]'(by simpa using h)

namespace Lex

open Parser

abbrev P := StringParse

def offset : P Nat := fun it => .ok it it.2.offset.byteIdx

def skipStr (s : String) : P Unit := fun it =>
  if (it.1.sliceFrom it.2).startsWith s then
    .ok ⟨it.1, it.2.nextn s.length⟩ ()
  else
    .err it (.other s!"expected '{s}'")

def peekIs (pred : Char → Bool) : P Bool := do
  return (← peekWhen? pred).isSome

/-- Consume the next character when it satisfies `pred`, reporting whether it was there. -/
def skipIf (pred : Char → Bool) : P Bool := do
  if (← peekIs pred) then
    skip
    return true
  return false

def expect (c : Char) (what : String) : P Unit := do
  unless (← skipIf (· == c)) do fail s!"expected {what}"

/-- Success consumes input; use `lookAhead` as well when only testing a prefix. -/
def tried (p : P α) : P Bool :=
  (attempt p *> pure true) <|> pure false

/-- Discard characters without allocating an array of them. -/
def skipWhile (pred : Char → Bool) : P Unit := do
  while (← peekIs pred) do skip

/-! ## Trivia -/

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

partial def blockCommentBody : P Unit := do
  let c ← any
  if c == '*' && (← peekWhen? (· == '/')).isSome then skip else blockCommentBody

partial def skipTrivia : P Unit := do
  skipWhile isSpace
  if ← tried (skipStr "//") then
    skipWhile (· != '\n')
    skipTrivia
  else if ← tried (skipStr "/*") then
    blockCommentBody
    skipTrivia

/-! ## Identifiers and keywords -/

def isLetter (c : Char) : Bool := c == '_' || Unicode.isLetter c
def isIdentChar (c : Char) : Bool := isLetter c || Unicode.isDigit c

private def keyword? (text : String.Slice) : Option String :=
  match text.utf8ByteSize with
  | 2 =>
    if text.startsWith "go" then some "go"
    else if text.startsWith "if" then some "if"
    else none
  | 3 =>
    if text.startsWith "for" then some "for"
    else if text.startsWith "map" then some "map"
    else if text.startsWith "var" then some "var"
    else none
  | 4 =>
    if text.startsWith "case" then some "case"
    else if text.startsWith "chan" then some "chan"
    else if text.startsWith "else" then some "else"
    else if text.startsWith "func" then some "func"
    else if text.startsWith "goto" then some "goto"
    else if text.startsWith "type" then some "type"
    else none
  | 5 =>
    if text.startsWith "break" then some "break"
    else if text.startsWith "const" then some "const"
    else if text.startsWith "defer" then some "defer"
    else if text.startsWith "range" then some "range"
    else none
  | 6 =>
    if text.startsWith "import" then some "import"
    else if text.startsWith "return" then some "return"
    else if text.startsWith "select" then some "select"
    else if text.startsWith "struct" then some "struct"
    else if text.startsWith "switch" then some "switch"
    else none
  | 7 =>
    if text.startsWith "default" then some "default"
    else if text.startsWith "package" then some "package"
    else none
  | 8 => if text.startsWith "continue" then some "continue" else none
  | 9 => if text.startsWith "interface" then some "interface" else none
  | 11 => if text.startsWith "fallthrough" then some "fallthrough" else none
  | _ => none

def identifier : P TokenKind := fun it =>
  if h : ¬it.2.IsAtEnd then
    if isLetter (it.2.get h) then
      let stop := it.2.skipWhile isIdentChar
      let kind := match keyword? (it.1.slice it.2 stop String.Pos.le_skipWhile) with
        | some text => TokenKind.keyword text
        | none => TokenKind.identifier
      .ok ⟨it.1, stop⟩ kind
    else
      .err it (.other "expected identifier")
  else
    .err it .eof

/-! ## Numeric literals -/

def isBinDigit (c : Char) : Bool := c == '0' || c == '1'
def isOctDigit (c : Char) : Bool := '0' ≤ c && c ≤ '7'
def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- One or more digits, with `_` allowed only between two digits. -/
def digitSeq (pred : Char → Bool) : P Unit := do
  discard <| satisfy pred
  while (← peekIs fun c => pred c || c == '_') do
    -- Commit after '_': a missing digit must not become a separate identifier.
    discard <| skipIf (· == '_')
    discard <| satisfy pred

def exponent (marks : List Char) : P Bool := do
  if (← peekIs fun c => "eEpP".any (· == c) && !marks.contains c) then
    fail "exponent marker does not match the literal base"
  unless (← skipIf (marks.contains ·)) do return false
  -- Once the exponent starts, propagate errors instead of splitting "1e+" into tokens.
  discard <| skipIf (fun c => c == '+' || c == '-')
  digitSeq Char.isDigit
  return true

/-- Lexical shape of a numeric literal body, before the optional `i` suffix.
`legacyOctal` is an `08`-style literal: an error only if it stays an integer. -/
inductive NumBody where
  | int | float | legacyOctal

/-- Hexadecimal body; the `0x` prefix is already consumed. -/
def hexBody : P NumBody := do
  if (← skipIf (· == '_')) then
    unless (← peekIs isHexDigit) do fail "expected hexadecimal digit after '_'"
  let intDigits ← peekIs isHexDigit
  if intDigits then digitSeq isHexDigit
  let point ← skipIf (· == '.')
  let fracDigits ← if point then peekIs isHexDigit else pure false
  if fracDigits then digitSeq isHexDigit
  unless intDigits || fracDigits do fail "hexadecimal literal has no digits"
  if (← exponent ['p', 'P']) then return .float
  if point then fail "hexadecimal mantissa requires a 'p' exponent"
  return .int

/-- Binary or octal body; the base prefix is already consumed. -/
def radixBody (digit : Char → Bool) (digitError : String) : P NumBody := do
  discard <| skipIf (· == '_')
  Parser.label (digitSeq digit) digitError
  if (← peekIs fun c => c.isDigit || c == '.' || "eEpP".any (· == c)) then
    fail "invalid digit, radix point, or exponent for literal base"
  return .int

/-- Decimal integer or float, including the legacy `0600` octal form. -/
def decimalBody : P NumBody := do
  let zero ← peekIs (· == '0')
  let legacy ← if zero then
      tried (lookAhead do
        skipWhile fun c => isOctDigit c || c == '_'
        satisfy fun c => c == '8' || c == '9')
    else pure false
  digitSeq Char.isDigit
  let point ← skipIf (· == '.')
  if point then discard <| optional (digitSeq Char.isDigit)
  let exp ← exponent ['e', 'E']
  return if point || exp then .float else if legacy then .legacyOctal else .int

/-- The `0x`, `0b`, or `0o` prefix of a non-decimal literal, if present. -/
def basePrefix : P (Option Char) :=
  (some <$> attempt (satisfy (· == '0') *> satisfy fun c => "xXbBoO".any (· == c)))
    <|> pure none

def numberBody : P NumBody := do
  -- ".5" is a float; the driver routes '.' here only when a digit follows.
  if (← skipIf (· == '.')) then
    digitSeq Char.isDigit
    discard <| exponent ['e', 'E']
    return .float
  match ← basePrefix with
  | some mark =>
    if mark == 'x' || mark == 'X' then hexBody
    else if mark == 'b' || mark == 'B' then radixBody isBinDigit "expected binary digit"
    else radixBody isOctDigit "expected octal digit"
  | none => decimalBody

/-- Validate lexical form here; arbitrary-precision value evaluation belongs to a later pass. -/
def number : P TokenKind := do
  let body ← numberBody
  if (← peekIs (· == '_')) then fail "'_' must separate successive digits"
  if (← skipIf (· == 'i')) then return .imaginaryLiteral
  -- Delay legacy octal validation: 08 is invalid, but 08i and 08.0 are decimal literals.
  match body with
  | .int => return .intLiteral
  | .float => return .floatLiteral
  | .legacyOctal => fail "invalid digit in octal literal"

/-! ## Rune and string literals -/

def escapeDigits (base n : Nat) (initial : Nat := 0) : P Nat := do
  let mut value := initial
  for _ in [:n] do
    let c ← satisfy (if base == 8 then isOctDigit else isHexDigit)
    let digit := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
    value := value * base + digit
  return value

/-- The backslash is already consumed. `quote` is the delimiter this literal may escape. -/
def escape (quote : Char) : P Unit := do
  let c ← any
  if c == 'x' then discard <| escapeDigits 16 2
  else if c == 'u' || c == 'U' then
    let value ← escapeDigits 16 (if c == 'u' then 4 else 8)
    -- Unicode escapes denote scalar values; unlike byte escapes, surrogates are invalid.
    if value > 0x10ffff || (0xd800 ≤ value && value ≤ 0xdfff) then
      fail "escape is not a Unicode scalar value"
  else if isOctDigit c then
    let value ← escapeDigits 8 2 (c.toNat - '0'.toNat)
    if value > 255 then fail "octal escape exceeds 255"
  else unless "abfnrtv\\".any (· == c) || c == quote do fail s!"unknown escape sequence: \\{c}"

def runeLiteral : P TokenKind := do
  skip
  let c ← any
  if c == '\\' then escape '\''
  else if c == '\n' || c == '\'' then fail "empty or unterminated rune literal"
  expect '\'' "closing '"
  return .runeLiteral

partial def interpretedBody : P Unit := do
  let c ← any
  if c == '"' then return
  if c == '\n' then fail "newline in string literal"
  if c == '\\' then escape '"'
  interpretedBody

partial def rawBody : P Unit := do
  unless (← any) == '`' do rawBody

/-! ## Operators -/

/-- Longest match first. -/
def operators : List String :=
  ["<<=", ">>=", "&^=", "...",
   "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "&^",
   "&&", "||", "<-", "++", "--", "==", "!=", "<=", ">=", ":=",
   "+", "-", "*", "/", "%", "&", "|", "^", "<", ">", "=", "!",
   "(", ")", "[", "]", "{", "}", ",", ".", ":", "~"]

/-- ponytail: linear operator scan; use a trie if profiling shows this is a bottleneck. -/
def operator : P TokenKind :=
  operators.foldr (fun op rest => (attempt (skipStr op) *> pure (TokenKind.symbol op)) <|> rest)
    (fail "unexpected character")

/-! ## Driver -/

def tokenKind : P TokenKind := do
  match ← peek! with
  | ';' => skip; return .semicolon
  | '`' => skip; rawBody; return .stringLiteral
  | '"' => skip; interpretedBody; return .stringLiteral
  | '\'' => runeLiteral
  -- ".5" is a float, "." and "..." are operators; look ahead only at the prefix so that a
  -- malformed float cannot fall back to '.'.
  | '.' => if ← tried (lookAhead (skip *> satisfy Char.isDigit)) then number else operator
  | c => if c.isDigit then number else if isLetter c then identifier else operator

def token : P Token := do
  let start ← offset
  let kind ← tokenKind
  -- Leave trivia outside the span: semicolon insertion examines these source gaps.
  let stop ← offset
  skipTrivia
  return ⟨kind, ⟨start, stop⟩, false⟩

def tokens : P (Array Token) := do
  -- Go permits a UTF-8 BOM only at the start; spans still refer to the original bytes.
  discard <| optional (satisfy (· == '\uFEFF'))
  skipTrivia
  let result ← many token
  if ← isEof then return result
  fail s!"unexpected character '{← peek!}'"

end Lex

/-- Lex Go source into significant tokens with automatic semicolon insertion applied. -/
def lex (source : Source) : Except String (Array Token) := do
  let raw ← match Lex.tokens ⟨source.text, source.text.startPos⟩ with
    | .ok _ result => .ok result
    | .err it e =>
      let off := it.2.offset.byteIdx
      match source.position? off with
      | some p => .error s!"{p.line}:{p.column}: {e}"
      | none => .error s!"offset {off}: {e}"
  insertSemicolons source raw

end GoAot
