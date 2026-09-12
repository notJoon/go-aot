module

public import Compiler.Source
public import Compiler.Parser.Parser
public import Compiler.Parser.String
import Compiler.Unicode

public section

namespace GoAot

-- TODO: Use Keyword and Symbol enums when parser coverage grows so invalid spellings are unrepresentable.
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
-- Internal test seam for raw token validation; compiler callers use lex.
def Lexer.Internal.insertSemicolons (source : Source) (tokens : Array Token) : Except String (Array Token) := do
  let sourceSize := source.text.utf8ByteSize
  let mut result := Array.emptyWithCapacity tokens.size
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

private abbrev ScanResult (α : Type) := Parser.Result α (Sigma String.Pos)

@[always_inline, inline]
private def scanDone {s : String} (pos : s.Pos) (value : α) : ScanResult α :=
  .ok ⟨s, pos⟩ value

@[always_inline, inline]
private def scanFailed {s : String} (pos : s.Pos) (error : Parser.Error) : ScanResult α :=
  .err ⟨s, pos⟩ error

def offset : P Nat := fun it => .ok it it.2.offset.byteIdx

def skipStr (s : String) : P Unit := fun it =>
  if (it.1.sliceFrom it.2).startsWith s then
    .ok ⟨it.1, it.2.nextn s.length⟩ ()
  else
    .err it (.other s!"expected '{s}'")

@[inline]
def peekIs (pred : Char → Bool) : P Bool := fun it =>
  if h : ¬it.2.IsAtEnd then .ok it (pred (it.2.get h)) else .ok it false

/-- Consume the next character when it satisfies `pred`, reporting whether it was there. -/
@[inline]
def skipIf (pred : Char → Bool) : P Bool := fun it =>
  if h : ¬it.2.IsAtEnd then
    if pred (it.2.get h) then .ok ⟨it.1, it.2.next h⟩ true else .ok it false
  else
    .ok it false

def expect (c : Char) (what : String) : P Unit := do
  unless (← skipIf (· == c)) do fail s!"expected {what}"

/-- Success consumes input; use `lookAhead` as well when only testing a prefix. -/
def tried (p : P α) : P Bool :=
  (do
    let _ ← attempt p
    return true) <|> pure false

@[specialize]
private def skipWhilePos {s : String} (pos : s.Pos) (pred : Char → Bool) : s.Pos :=
  if h : ¬pos.IsAtEnd then
    if pred (pos.get h) then skipWhilePos (pos.next h) pred else pos
  else
    pos
termination_by pos

/-- Discard characters without allocating an array of them. -/
@[inline]
def skipWhile (pred : Char → Bool) : P Unit := fun it =>
  .ok ⟨it.1, skipWhilePos it.2 pred⟩ ()

/-! ## Trivia -/

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

private def scanBlockComment {s : String} (pos : s.Pos) : ScanResult Unit :=
  if h : ¬pos.IsAtEnd then
    let next := pos.next h
    if pos.get h == '*' then
      if h' : ¬next.IsAtEnd then
        if next.get h' == '/' then scanDone (next.next h') () else scanBlockComment next
      else
        scanBlockComment next
    else
      scanBlockComment next
  else
    scanFailed pos (.other "expected any element")
termination_by pos

def blockCommentBody : P Unit := fun it =>
  scanBlockComment it.2

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
@[specialize]
private def scanDigitSeq {s : String} (pos : s.Pos) (pred : Char → Bool) : ScanResult Unit :=
  if h : ¬pos.IsAtEnd then
    let c := pos.get h
    if pred c then
      scanDigitSeq (pos.next h) pred
    else if c == '_' then
      let next := pos.next h
      if h' : ¬next.IsAtEnd then
        if pred (next.get h') then scanDigitSeq (next.next h') pred
        else scanFailed next (.other "satisfy: predicate not satisfied")
      else
        scanFailed next (.other "expected any element")
    else
      scanDone pos ()
  else
    scanDone pos ()
termination_by pos

@[inline]
def digitSeq (pred : Char → Bool) : P Unit := fun it =>
  if h : ¬it.2.IsAtEnd then
    if pred (it.2.get h) then scanDigitSeq (it.2.next h) pred
    else scanFailed it.2 (.other "satisfy: predicate not satisfied")
  else
    scanFailed it.2 (.other "expected any element")

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

/-- The base selected by a non-decimal literal prefix. -/
private inductive NumBase where
  | binary | octal | hexadecimal

/-- The `0x`, `0b`, or `0o` prefix of a non-decimal literal, if present. -/
private def basePrefix : P (Option NumBase) :=
  optional <| attempt do
    let _ ← satisfy (· == '0')
    match ← any with
    | 'x' | 'X' => return .hexadecimal
    | 'b' | 'B' => return .binary
    | 'o' | 'O' => return .octal
    | _ => fail "expected base prefix"

def numberBody : P NumBody := do
  -- ".5" is a float; the driver routes '.' here only when a digit follows.
  if (← skipIf (· == '.')) then
    digitSeq Char.isDigit
    discard <| exponent ['e', 'E']
    return .float
  match ← basePrefix with
  | some .hexadecimal => hexBody
  | some .binary => radixBody isBinDigit "expected binary digit"
  | some .octal => radixBody isOctDigit "expected octal digit"
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

@[inline]
private def digitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

/--
A numeric escape's radix, digit width, and completion rule.
-/
private inductive EscapeKind where
  | hexByte | unicode4 | unicode8 | octal

@[inline]
private def EscapeKind.base : EscapeKind → Nat
  | .octal => 8
  | .hexByte | .unicode4 | .unicode8 => 16

@[inline]
private def EscapeKind.width : EscapeKind → Nat
  | .hexByte => 2
  | .unicode4 => 4
  | .unicode8 => 8
  | .octal => 3

@[inline]
private def EscapeKind.accepts : EscapeKind → Char → Bool
  | .octal, c => isOctDigit c
  | .hexByte, c | .unicode4, c | .unicode8, c => isHexDigit c

@[inline]
private def isUnicodeScalar (value : Nat) : Bool :=
  decide value.isValidChar

private def EscapeKind.completionError? (kind : EscapeKind) (value : Nat) : Option String :=
  match kind with
  | .octal => if value < UInt8.size then none else some "octal escape exceeds 255"
  | .unicode4 | .unicode8 =>
    if isUnicodeScalar value then none else some "escape is not a Unicode scalar value"
  | .hexByte => none

private def scanEscapeDigits {s : String} (pos : s.Pos) (kind : EscapeKind)
    (remaining value : Nat) :
    ScanResult Nat :=
  match remaining with
  | 0 => scanDone pos value
  | remaining + 1 =>
    if h : ¬pos.IsAtEnd then
      let c := pos.get h
      if kind.accepts c then
        scanEscapeDigits (pos.next h) kind remaining (value * kind.base + digitValue c)
      else
        scanFailed pos (.other "satisfy: predicate not satisfied")
    else
      scanFailed pos (.other "expected any element")
termination_by remaining

private def escapeDigits (kind : EscapeKind) (n : Nat := kind.width) (initial : Nat := 0) :
    P Nat := fun it =>
  scanEscapeDigits it.2 kind n initial

/--
The backslash is already consumed.
`quote` is the delimiter this literal may escape.
-/
def escape (quote : Char) : P Unit := do
  let c ← any
  if c == 'x' then discard <| escapeDigits .hexByte
  else if c == 'u' || c == 'U' then
    let kind := if c == 'u' then EscapeKind.unicode4 else .unicode8
    let value ← escapeDigits kind
    -- Unicode escapes denote scalar values. Surrogates are invalid.
    if let some error := kind.completionError? value then
      fail error
  else if isOctDigit c then
    let value ← escapeDigits .octal (EscapeKind.octal.width - 1) (c.toNat - '0'.toNat)
    if let some error := EscapeKind.octal.completionError? value then fail error
  else unless "abfnrtv\\".any (· == c) || c == quote do fail s!"unknown escape sequence: \\{c}"

def runeLiteral : P TokenKind := do
  skip
  let c ← any
  if c == '\\' then escape '\''
  else if c == '\n' || c == '\'' then fail "empty or unterminated rune literal"
  expect '\'' "closing '"
  return .runeLiteral

/--
The state of an interpreted string scan. Numeric states begin at their first digit.
The nullary cases keep the scanner tail recursive without allocations.
-/
private inductive InterpretedState where
  | normal | hexByte | unicode4 | unicode8 | octal

/--
Returns the state after a consumed escape introducer.

Octal is handled separately so its first digit remains available
to the digit scanner.
-/
private def InterpretedState.afterEscape? (escaped : Char) : Option InterpretedState :=
  match escaped with
  | 'x' => some .hexByte
  | 'u' => some .unicode4
  | 'U' => some .unicode8
  | c =>
    if "abfnrtv\\\"".any (· == c) then some .normal
    else none

-- The secondary termination measure permits dispatch to a digit state before the position advances.
mutual
  private def scanInterpreted {s : String} (pos : s.Pos) (state : InterpretedState) :
      ScanResult Unit :=
    match state with
    | .hexByte => scanInterpretedDigits pos .hexByte EscapeKind.hexByte.width 0
    | .unicode4 => scanInterpretedDigits pos .unicode4 EscapeKind.unicode4.width 0
    | .unicode8 => scanInterpretedDigits pos .unicode8 EscapeKind.unicode8.width 0
    | .octal => scanInterpretedDigits pos .octal EscapeKind.octal.width 0
    | .normal =>
      if h : ¬pos.IsAtEnd then
        let c := pos.get h
        let next := pos.next h
        if c == '"' then
          scanDone next ()
        else if c == '\n' then
          scanFailed next (.other "newline in string literal")
        else if c == '\\' then
          if h' : ¬next.IsAtEnd then
            let escaped := next.get h'
            let after := next.next h'
            if isOctDigit escaped then
              scanInterpreted next .octal
            else
              match InterpretedState.afterEscape? escaped with
              | some state => scanInterpreted after state
              | none => scanFailed after (.other s!"unknown escape sequence: \\{escaped}")
          else
            scanFailed next (.other "expected any element")
        else
          scanInterpreted next .normal
      else
        scanFailed pos (.other "expected any element")
  termination_by (pos, 1)

  /--
  Consumes exactly `remaining` digits, then validates the completed escape and
  resumes the normal string scan.

  Callers maintain `remaining > 0`. The radix accumulator is `value`.
  -/
  private def scanInterpretedDigits {s : String} (pos : s.Pos) (kind : EscapeKind)
      (remaining value : Nat) : ScanResult Unit :=
    if h : ¬pos.IsAtEnd then
      let c := pos.get h
      let next := pos.next h
      if kind.accepts c then
        let value := value * kind.base + digitValue c
        match remaining with
        | 0 => scanFailed pos (.other "expected any element")
        | 1 =>
          match kind.completionError? value with
          | some error => scanFailed next (.other error)
          | none => scanInterpreted next .normal
        | remaining + 2 => scanInterpretedDigits next kind (remaining + 1) value
      else
        scanFailed pos (.other "satisfy: predicate not satisfied")
    else
      scanFailed pos (.other "expected any element")
  termination_by (pos, 0)
end

def interpretedBody : P Unit := fun it =>
  scanInterpreted it.2 .normal

private def scanRaw {s : String} (pos : s.Pos) : ScanResult Unit :=
  if h : ¬pos.IsAtEnd then
    let next := pos.next h
    if pos.get h == '`' then scanDone next () else scanRaw next
  else
    scanFailed pos (.other "expected any element")
termination_by pos

def rawBody : P Unit := fun it =>
  scanRaw it.2

/-! ## Operators -/

private def scanEqualSuffix {s : String} (pos : s.Pos) (single combined : String) :
    ScanResult TokenKind :=
  if h : ¬pos.IsAtEnd then
    if pos.get h == '=' then scanDone (pos.next h) (.symbol combined)
    else scanDone pos (.symbol single)
  else
    scanDone pos (.symbol single)

private def scanDuplicateOrEqual {s : String} (pos : s.Pos) (duplicate : Char)
    (single doubled combined : String) : ScanResult TokenKind :=
  if h : ¬pos.IsAtEnd then
    let c := pos.get h
    if c == duplicate then scanDone (pos.next h) (.symbol doubled)
    else if c == '=' then scanDone (pos.next h) (.symbol combined)
    else scanDone pos (.symbol single)
  else
    scanDone pos (.symbol single)

private def scanLess {s : String} (pos : s.Pos) : ScanResult TokenKind :=
  if h : ¬pos.IsAtEnd then
    match pos.get h with
    | '<' => scanEqualSuffix (pos.next h) "<<" "<<="
    | '-' => scanDone (pos.next h) (.symbol "<-")
    | '=' => scanDone (pos.next h) (.symbol "<=")
    | _ => scanDone pos (.symbol "<")
  else
    scanDone pos (.symbol "<")

private def scanAmpersand {s : String} (pos : s.Pos) : ScanResult TokenKind :=
  if h : ¬pos.IsAtEnd then
    match pos.get h with
    | '^' => scanEqualSuffix (pos.next h) "&^" "&^="
    | '&' => scanDone (pos.next h) (.symbol "&&")
    | '=' => scanDone (pos.next h) (.symbol "&=")
    | _ => scanDone pos (.symbol "&")
  else
    scanDone pos (.symbol "&")

private def scanDots {s : String} (pos : s.Pos) : ScanResult TokenKind :=
  if h : ¬pos.IsAtEnd then
    let next := pos.next h
    if pos.get h == '.' then
      if h' : ¬next.IsAtEnd then
        if next.get h' == '.' then scanDone (next.next h') (.symbol "...")
        else scanDone pos (.symbol ".")
      else
        scanDone pos (.symbol ".")
    else
      scanDone pos (.symbol ".")
  else
    scanDone pos (.symbol ".")

private def scanOperator {s : String} (pos : s.Pos) : ScanResult TokenKind :=
  if h : ¬pos.IsAtEnd then
    let next := pos.next h
    match pos.get h with
    | '+' => scanDuplicateOrEqual next '+' "+" "++" "+="
    | '-' => scanDuplicateOrEqual next '-' "-" "--" "-="
    | '*' => scanEqualSuffix next "*" "*="
    | '/' => scanEqualSuffix next "/" "/="
    | '%' => scanEqualSuffix next "%" "%="
    | '&' => scanAmpersand next
    | '|' => scanDuplicateOrEqual next '|' "|" "||" "|="
    | '^' => scanEqualSuffix next "^" "^="
    | '<' => scanLess next
    | '>' =>
      if h' : ¬next.IsAtEnd then
        match next.get h' with
        | '>' => scanEqualSuffix (next.next h') ">>" ">>="
        | '=' => scanDone (next.next h') (.symbol ">=")
        | _ => scanDone next (.symbol ">")
      else
        scanDone next (.symbol ">")
    | '=' => scanEqualSuffix next "=" "=="
    | '!' => scanEqualSuffix next "!" "!="
    | '(' => scanDone next (.symbol "(")
    | ')' => scanDone next (.symbol ")")
    | '[' => scanDone next (.symbol "[")
    | ']' => scanDone next (.symbol "]")
    | '{' => scanDone next (.symbol "{")
    | '}' => scanDone next (.symbol "}")
    | ',' => scanDone next (.symbol ",")
    | '.' => scanDots next
    | ':' => scanEqualSuffix next ":" ":="
    | '~' => scanDone next (.symbol "~")
    | _ => scanFailed pos (.other "unexpected character")
  else
    scanFailed pos (.other "unexpected character")

/--
Dispatch on at most three characters without constructing parser alternatives or scanning a list.
-/
def operator : P TokenKind := fun it =>
  scanOperator it.2

/-! ## Driver -/

def tokenKind : P TokenKind := do
  match ← peek! with
  | ';' => skip; return .semicolon
  | '`' => skip; rawBody; return .stringLiteral
  | '"' => skip; interpretedBody; return .stringLiteral
  | '\'' => runeLiteral
  -- ".5" is a float, "." and "..." are operators; look ahead only at the prefix so that a
  -- malformed float cannot fall back to '.'.
  | '.' =>
    if ← tried (lookAhead do
      skip
      satisfy Char.isDigit) then number else operator
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
  Lexer.Internal.insertSemicolons source raw

end GoAot
