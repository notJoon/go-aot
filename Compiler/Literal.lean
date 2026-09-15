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
