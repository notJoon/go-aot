module

public section

namespace GoAot.Literal

/-- `isBinDigit '1' = true`, `isBinDigit '2' = false` -/
def isBinDigit (c : Char) : Bool := c == '0' || c == '1'
/-- `isOctDigit '7' = true`, `isOctDigit '8' = false` -/
def isOctDigit (c : Char) : Bool := '0' ≤ c && c ≤ '7'
/-- `isHexDigit 'F' = true`, `isHexDigit 'g' = false` -/
def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Callers must pass a character accepted by `isHexDigit`. `digitValue '7' = 7`, `digitValue 'F' = 15` -/
@[inline]
def digitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

/-- Decode an integer literal already validated by the lexer. -/
def decodeInt (literal : String.Slice) : Nat := Id.run do
  let (base, digits) :=
    if literal.startsWith "0" then
      match (literal.drop 1).front? with
      | some 'x' | some 'X' => (16, literal.drop 2)
      | some 'b' | some 'B' => (2, literal.drop 2)
      | some 'o' | some 'O' => (8, literal.drop 2)
      | _ => (8, literal)
    else (10, literal)
  return digits.foldl (fun value c =>
    if c == '_' then value else value * base + digitValue c) 0

/--
Decode a decimal floating-point literal already validated by the lexer into its exact value.
Returns `none` for hexadecimal literals.
Example: `decodeFloat? "1_0.5e-1" = some (21 / 20)`.
-/
def decodeFloat? (literal : String.Slice) : Option Rat := Id.run do
  if literal.startsWith "0x" || literal.startsWith "0X" then return none
  let mut mantissa := 0
  let mut scale : Int := 0
  let mut fraction := false
  let mut inExponent := false
  let mut exponentNegative := false
  let mut exponent : Int := 0
  for c in literal.copy.toList do
    if c == '_' || c == '+' then continue
    if inExponent then
      if c == '-' then exponentNegative := true
      else exponent := exponent * 10 + (digitValue c : Int)
    else if c == '.' then fraction := true
    else if c == 'e' || c == 'E' then inExponent := true
    else
      mantissa := mantissa * 10 + digitValue c
      if fraction then scale := scale - 1
  let power := scale + (if exponentNegative then -exponent else exponent)
  return some (OfScientific.ofScientific mantissa (power < 0) power.natAbs)

/--
The float64 nearest to `value`, with ties to even, as Go converts an untyped constant.
Values beyond the largest finite float64 become an infinity.
Example: `toFloat (3 / 10) = 0.3`.
-/
def toFloat (value : Rat) : Float := Id.run do
  let numerator := value.num.natAbs
  let denominator := value.den
  if numerator == 0 then return 0
  -- `numerator / denominator` lies in (2^(k - 1), 2^(k + 1)) for k = log2 numerator - log2 denominator.
  let divide (exponent : Int) : Nat × Nat × Nat :=
    let scaled := if exponent < 0 then numerator * 2 ^ exponent.natAbs else numerator
    let divisor := if exponent < 0 then denominator else denominator * 2 ^ exponent.natAbs
    (scaled / divisor, scaled % divisor, divisor)
  let mut exponent : Int := max ((numerator.log2 : Int) - denominator.log2 - 53) (-1074)
  let mut (quotient, remainder, divisor) := divide exponent
  if quotient ≥ 2 ^ 53 then
    exponent := exponent + 1
    (quotient, remainder, divisor) := divide exponent
  if 2 * remainder > divisor || (2 * remainder == divisor && quotient % 2 == 1) then
    quotient := quotient + 1
  if quotient == 2 ^ 53 then
    quotient := 2 ^ 52
    exponent := exponent + 1
  -- The quotient has at most 53 bits, so scaling it by a power of two is exact.
  let magnitude := if exponent > 971 then 1 / 0 else (Float.ofNat quotient).scaleB exponent
  return if value.num < 0 then -magnitude else magnitude

#guard [("0.1", 0.1), ("0.3", 0.3), ("1e-5", 1e-5), ("123456789.0", 123456789.0),
    ("1.7976931348623157e308", 1.7976931348623157e308), ("5e-324", 5e-324), ("2.5e-324", 5e-324),
    ("2.4e-324", 0), ("2.2250738585072011e-308", 2.2250738585072011e-308),
    ("9007199254740993", 9007199254740992), ("9007199254740995", 9007199254740996)].all
  fun (text, expected) => (decodeFloat? text.toSlice).map toFloat == some expected
#guard toFloat (1 / 10 + 2 / 10) == 0.3 && toFloat (-3 / 2) == -1.5
#guard (toFloat (OfScientific.ofScientific 18 false 307)).isInf

/--
A numeric escape's radix, digit width, and completion rule.
-/
inductive EscapeKind where
  /--
  `\x` followed by exactly two hexadecimal digits, denoting a single byte.

  Example: `"\x41"` is the byte `0x41` (`A`), and `"\xff"` is the byte `0xFF`.
  -/
  | hexByte
  /--
  `\u` followed by exactly four hexadecimal digits, denoting a Unicode code point
  encoded as UTF-8. Surrogate halves are rejected.

  Example: `"\u00e9"` is `é`, encoded as the bytes `0xC3 0xA9`. `"\ud800"` is invalid.
  -/
  | unicode4
  /--
  `\U` followed by exactly eight hexadecimal digits, denoting a Unicode code point
  encoded as UTF-8. Values above `0x10FFFF` and surrogate halves are rejected.

  Example: `"\U0001F600"` is `😀`, encoded as four bytes. `"\U00110000"` is invalid.
  -/
  | unicode8
  /--
  `\` followed by exactly three octal digits, denoting a single byte. Values above 255 are rejected.

  Example: `"\101"` is the byte `0x41` (`A`), and `"\400"` is invalid.
  -/
  | octal

/-- `EscapeKind.octal.base = 8`, `EscapeKind.unicode4.base = 16` -/
@[inline]
def EscapeKind.base : EscapeKind → Nat
  | .octal => 8
  | .hexByte | .unicode4 | .unicode8 => 16

/-- `EscapeKind.hexByte.width = 2` (`\x41`), `EscapeKind.unicode8.width = 8` (`\U0001F600`) -/
@[inline]
def EscapeKind.width : EscapeKind → Nat
  | .hexByte => 2
  | .unicode4 => 4
  | .unicode8 => 8
  | .octal => 3

/-- `EscapeKind.octal.accepts '7' = true`, `EscapeKind.octal.accepts '8' = false` -/
@[inline]
def EscapeKind.accepts : EscapeKind → Char → Bool
  | .octal, c => isOctDigit c
  | .hexByte, c | .unicode4, c | .unicode8, c => isHexDigit c

/--
`EscapeKind.octal.completionError? 256 = some "octal escape exceeds 255"`,
`EscapeKind.unicode4.completionError? 0xD800 = some "escape is not a Unicode scalar value"`,
`EscapeKind.hexByte.completionError? 0xFF = none`
-/
def EscapeKind.completionError? (kind : EscapeKind) (value : Nat) : Option String :=
  match kind with
  | .octal => if value < UInt8.size then none else some "octal escape exceeds 255"
  | .unicode4 | .unicode8 =>
    if decide value.isValidChar then none else some "escape is not a Unicode scalar value"
  | .hexByte => none

/-- The quote is excluded because runes and strings escape different delimiters.
`simpleEscape? 'n' = some 10`, `simpleEscape? '"' = none` -/
def simpleEscape? : Char → Option UInt8
  | 'a' => some 7 | 'b' => some 8 | 'f' => some 12 | 'n' => some 10
  | 'r' => some 13 | 't' => some 9 | 'v' => some 11
  | '\\' => some 92
  | _ => none

/--
Decode an interpreted string literal once at the semantic boundary so backends never reinterpret Go syntax.
The input keeps its surrounding quotes and must already be accepted by the lexer, which validates escapes.
Unescaped bytes are copied as they are because `\` never occurs inside a multibyte UTF-8 sequence.

`decodeInterpreted "\"a\\x41\\n\""` is the bytes `[97, 65, 10]`
-/
def decodeInterpreted (literal : String) : ByteArray := Id.run do
  let byte (i : Nat) : UInt8 :=
    if h : i < literal.utf8ByteSize then literal.getUTF8Byte ⟨i⟩ h else 0
  let digits (kind : EscapeKind) (start : Nat) : Nat := Id.run do
    let mut value := 0
    for i in [start:start + kind.width] do
      value := value * kind.base + digitValue (Char.ofUInt8 (byte i))
    return value
  let stop := literal.utf8ByteSize - 1
  let mut bytes := ByteArray.empty
  let mut i := 1
  while i < stop do
    if byte i != '\\'.toUInt8 then
      bytes := bytes.push (byte i)
      i := i + 1
    else
      let escaped := Char.ofUInt8 (byte (i + 1))
      if let some value := simpleEscape? escaped then
        bytes := bytes.push value
        i := i + 2
      else if escaped == '"' then
        bytes := bytes.push 34
        i := i + 2
      else if escaped == 'x' then
        bytes := bytes.push (digits .hexByte (i + 2)).toUInt8
        i := i + 2 + EscapeKind.hexByte.width
      else if escaped == 'u' || escaped == 'U' then
        let kind := if escaped == 'u' then EscapeKind.unicode4 else .unicode8
        for value in String.utf8EncodeChar (Char.ofNat (digits kind (i + 2))) do
          bytes := bytes.push value
        i := i + 2 + kind.width
      else
        -- The lexer admits only octal escapes past this point.
        bytes := bytes.push (digits .octal (i + 1)).toUInt8
        i := i + 1 + EscapeKind.octal.width
  return bytes

end GoAot.Literal
