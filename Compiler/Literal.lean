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

private def takeDigits (kind : EscapeKind) : Nat → Nat → List Char → Except String (Nat × List Char)
  | 0, value, rest => return (value, rest)
  | count + 1, value, c :: rest =>
    if kind.accepts c then takeDigits kind count (value * kind.base + digitValue c) rest
    else throw "invalid string escape"
  | _, _, [] => throw "incomplete string escape"

private def pushChar (bytes : ByteArray) (c : Char) : ByteArray := Id.run do
  let mut result := bytes
  for byte in (String.singleton c).toUTF8 do result := result.push byte
  return result

/--
Decode source escapes once at the semantic boundary so backends never reinterpret Go syntax.
The input is the literal body without its surrounding quotes.

`decodeInterpreted "a\\x41\\n".toList = .ok` bytes `[97, 65, 10]`,
`decodeInterpreted "\\q".toList = .error "invalid string escape"`,
`decodeInterpreted "\\x4".toList = .error "incomplete string escape"`
-/
partial def decodeInterpreted (chars : List Char) (bytes : ByteArray := .empty) :
    Except String ByteArray := do
  match chars with
  | [] => return bytes
  | '\\' :: escaped :: rest =>
    if let some byte := simpleEscape? escaped then
      decodeInterpreted rest (bytes.push byte)
    else if escaped == '"' then
      decodeInterpreted rest (bytes.push 34)
    else if escaped == 'x' then
      let (value, rest) ← takeDigits .hexByte EscapeKind.hexByte.width 0 rest
      decodeInterpreted rest (bytes.push value.toUInt8)
    else if escaped == 'u' || escaped == 'U' then
      let kind := if escaped == 'u' then EscapeKind.unicode4 else .unicode8
      let (value, rest) ← takeDigits kind kind.width 0 rest
      decodeInterpreted rest (pushChar bytes (Char.ofNat value))
    else if isOctDigit escaped then
      let (value, rest) ← takeDigits .octal (EscapeKind.octal.width - 1) (digitValue escaped) rest
      decodeInterpreted rest (bytes.push value.toUInt8)
    else
      throw "invalid string escape"
  | '\\' :: [] => throw "incomplete string escape"
  | c :: rest => decodeInterpreted rest (pushChar bytes c)

end GoAot.Literal
