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

private def lexError (text : String) : Option String :=
  match lex (Source.ofString text) with
  | .error diagnostic => some (diagnostic.render (Source.ofString text))
  | .ok _ => none

private def kindName : TokenKind → String
  | .identifier => "identifier" | .intLiteral => "int" | .floatLiteral => "float"
  | .imaginaryLiteral => "imaginary" | .runeLiteral => "rune" | .stringLiteral => "string"
  | .keyword text => s!"keyword {text}" | .symbol text => s!"'{text}'" | .semicolon => ";"

/-- The tokens of `text` with their spans, or where lexing failed and why. -/
private def showTokens (text : String) : String :=
  match lex (Source.ofString text) with
  | .ok tokens => ", ".intercalate (tokens.map fun t => s!"{kindName t.kind} {t.span.start}-{t.span.stop}").toList
  | .error diagnostic => s!"error {diagnostic.render (Source.ofString text)}"

/-- The positions where semicolons are inserted after `tokens`, or why the tokens are rejected. -/
private def showSemis (text : String) (tokens : Array Token) : String :=
  match Lexer.Internal.insertSemicolons (Source.ofString text) tokens with
  | .ok result => s!"inserted at {(result.filter (·.inserted)).map (·.span.start)}"
  | .error diagnostic => s!"error {diagnostic.message}"

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
-- Tokens that end a statement get a semicolon at the end of the line, and others do not.
/--
info: x: inserted at #[1]
1: inserted at #[1]
1.0: inserted at #[3]
1i: inserted at #[2]
'a': inserted at #[3]
"a": inserted at #[3]
break: inserted at #[5]
continue: inserted at #[8]
fallthrough: inserted at #[11]
return: inserted at #[6]
++: inserted at #[2]
--: inserted at #[2]
): inserted at #[1]
]: inserted at #[1]
}: inserted at #[1]
if: inserted at #[]
for: inserted at #[]
else: inserted at #[]
func: inserted at #[]
goto: inserted at #[]
-/
#guard_msgs in
#eval show IO Unit from do
  for (kind, spelling) in [(TokenKind.identifier, "x"), (.intLiteral, "1"), (.floatLiteral, "1.0"),
      (.imaginaryLiteral, "1i"), (.runeLiteral, "'a'"), (.stringLiteral, "\"a\""),
      (.keyword "break", "break"), (.keyword "continue", "continue"),
      (.keyword "fallthrough", "fallthrough"), (.keyword "return", "return"),
      (.symbol "++", "++"), (.symbol "--", "--"), (.symbol ")", ")"),
      (.symbol "]", "]"), (.symbol "}", "}"), (.keyword "if", "if"), (.keyword "for", "for"),
      (.keyword "else", "else"), (.keyword "func", "func"), (.keyword "goto", "goto")] do
    IO.println s!"{spelling}: {showSemis spelling #[token kind 0 spelling.utf8ByteSize]}"
-- Invalid spans are rejected.
/--
info: error expected ordered, nonempty source token spans within the source
error expected ordered, nonempty source token spans within the source
error expected ordered, nonempty source token spans within the source
-/
#guard_msgs in
#eval show IO Unit from do
  for tokens in [#[ident 1 0], #[ident 0 2], #[ident 0 1, ident 0 1]] do
    IO.println (showSemis "x" tokens)
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
#guard lexes "  \t\n // c \n /* a\nb */ " #[]
#guard lexes "/**//*/*/x" #[(.identifier, 9, 10), (.semicolon, 10, 10)]
#guard lexes "package main" #[(.keyword "package", 0, 7), (.identifier, 8, 12), (.semicolon, 12, 12)]
#guard lexes "_x9 가b" #[(.identifier, 0, 3), (.identifier, 4, 8), (.semicolon, 8, 8)]
-- A keyword is a keyword only when no identifier character follows it.
/--
info: break x: keyword break 0-5, identifier 6-7, ; 7-7 | breakx: identifier 0-6, ; 6-6
case x: keyword case 0-4, identifier 5-6, ; 6-6 | casex: identifier 0-5, ; 5-5
chan x: keyword chan 0-4, identifier 5-6, ; 6-6 | chanx: identifier 0-5, ; 5-5
const x: keyword const 0-5, identifier 6-7, ; 7-7 | constx: identifier 0-6, ; 6-6
continue x: keyword continue 0-8, identifier 9-10, ; 10-10 | continuex: identifier 0-9, ; 9-9
default x: keyword default 0-7, identifier 8-9, ; 9-9 | defaultx: identifier 0-8, ; 8-8
defer x: keyword defer 0-5, identifier 6-7, ; 7-7 | deferx: identifier 0-6, ; 6-6
else x: keyword else 0-4, identifier 5-6, ; 6-6 | elsex: identifier 0-5, ; 5-5
fallthrough x: keyword fallthrough 0-11, identifier 12-13, ; 13-13 | fallthroughx: identifier 0-12, ; 12-12
for x: keyword for 0-3, identifier 4-5, ; 5-5 | forx: identifier 0-4, ; 4-4
func x: keyword func 0-4, identifier 5-6, ; 6-6 | funcx: identifier 0-5, ; 5-5
go x: keyword go 0-2, identifier 3-4, ; 4-4 | gox: identifier 0-3, ; 3-3
goto x: keyword goto 0-4, identifier 5-6, ; 6-6 | gotox: identifier 0-5, ; 5-5
if x: keyword if 0-2, identifier 3-4, ; 4-4 | ifx: identifier 0-3, ; 3-3
import x: keyword import 0-6, identifier 7-8, ; 8-8 | importx: identifier 0-7, ; 7-7
interface x: keyword interface 0-9, identifier 10-11, ; 11-11 | interfacex: identifier 0-10, ; 10-10
map x: keyword map 0-3, identifier 4-5, ; 5-5 | mapx: identifier 0-4, ; 4-4
package x: keyword package 0-7, identifier 8-9, ; 9-9 | packagex: identifier 0-8, ; 8-8
range x: keyword range 0-5, identifier 6-7, ; 7-7 | rangex: identifier 0-6, ; 6-6
return x: keyword return 0-6, identifier 7-8, ; 8-8 | returnx: identifier 0-7, ; 7-7
select x: keyword select 0-6, identifier 7-8, ; 8-8 | selectx: identifier 0-7, ; 7-7
struct x: keyword struct 0-6, identifier 7-8, ; 8-8 | structx: identifier 0-7, ; 7-7
switch x: keyword switch 0-6, identifier 7-8, ; 8-8 | switchx: identifier 0-7, ; 7-7
type x: keyword type 0-4, identifier 5-6, ; 6-6 | typex: identifier 0-5, ; 5-5
var x: keyword var 0-3, identifier 4-5, ; 5-5 | varx: identifier 0-4, ; 4-4
-/
#guard_msgs in
#eval show IO Unit from do
  for word in ["break", "case", "chan", "const", "continue", "default", "defer", "else",
      "fallthrough", "for", "func", "go", "goto", "if", "import", "interface", "map",
      "package", "range", "return", "select", "struct", "switch", "type", "var"] do
    IO.println s!"{word} x: {showTokens (word ++ " x")} | {word}x: {showTokens (word ++ "x")}"
#guard lexes "a<<=b" #[(.identifier, 0, 1), (.symbol "<<=", 1, 4), (.identifier, 4, 5), (.semicolon, 5, 5)]
#guard lexes "a&^=b" #[(.identifier, 0, 1), (.symbol "&^=", 1, 4), (.identifier, 4, 5), (.semicolon, 5, 5)]
#guard lexes "f(x...)" #[(.identifier, 0, 1), (.symbol "(", 1, 2), (.identifier, 2, 3),
  (.symbol "...", 3, 6), (.symbol ")", 6, 7), (.semicolon, 7, 7)]
#guard lexes "a.b" #[(.identifier, 0, 1), (.symbol ".", 1, 2), (.identifier, 2, 3), (.semicolon, 3, 3)]
#guard lexes "x<-y" #[(.identifier, 0, 1), (.symbol "<-", 1, 3), (.identifier, 3, 4), (.semicolon, 4, 4)]
/--
info: <<=  '<<=' 0-3
>>=  '>>=' 0-3
&^=  '&^=' 0-3
...  '...' 0-3
+=  '+=' 0-2
-=  '-=' 0-2
*=  '*=' 0-2
/=  '/=' 0-2
%=  '%=' 0-2
&=  '&=' 0-2
|=  '|=' 0-2
^=  '^=' 0-2
<<  '<<' 0-2
>>  '>>' 0-2
&^  '&^' 0-2
&&  '&&' 0-2
||  '||' 0-2
<-  '<-' 0-2
++  '++' 0-2, ; 2-2
--  '--' 0-2, ; 2-2
==  '==' 0-2
!=  '!=' 0-2
<=  '<=' 0-2
>=  '>=' 0-2
:=  ':=' 0-2
+  '+' 0-1
-  '-' 0-1
*  '*' 0-1
/  '/' 0-1
%  '%' 0-1
&  '&' 0-1
|  '|' 0-1
^  '^' 0-1
<  '<' 0-1
>  '>' 0-1
=  '=' 0-1
!  '!' 0-1
(  '(' 0-1
)  ')' 0-1, ; 1-1
[  '[' 0-1
]  ']' 0-1, ; 1-1
{  '{' 0-1
}  '}' 0-1, ; 1-1
,  ',' 0-1
.  '.' 0-1
:  ':' 0-1
~  '~' 0-1
-/
#guard_msgs in
#eval show IO Unit from do
  for spelling in operatorSpellings do IO.println s!"{spelling}  {showTokens spelling}"

-- Literal classification.
/--
info: "0"  int 0-1, ; 1-1
"42"  int 0-2, ; 2-2
"1_000"  int 0-5, ; 5-5
"0600"  int 0-4, ; 4-4
"0o600"  int 0-5, ; 5-5
"0b_1010"  int 0-7, ; 7-7
"0B1"  int 0-3, ; 3-3
"0O7"  int 0-3, ; 3-3
"0xBadFace"  int 0-9, ; 9-9
"0X_67_7a"  int 0-8, ; 8-8
"0."  float 0-2, ; 2-2
".25"  float 0-3, ; 3-3
"72.40"  float 0-5, ; 5-5
"1e9"  float 0-3, ; 3-3
"1E-6"  float 0-4, ; 4-4
"1_5.2e+3"  float 0-8, ; 8-8
"0x1p-2"  float 0-6, ; 6-6
"0x_1FFFp-16"  float 0-11, ; 11-11
"0x.1p4"  float 0-6, ; 6-6
"0i"  imaginary 0-2, ; 2-2
"2.71828i"  imaginary 0-8, ; 8-8
"1e6i"  imaginary 0-4, ; 4-4
"0x1p-2i"  imaginary 0-7, ; 7-7
"'a'"  rune 0-3, ; 3-3
"'\\n'"  rune 0-4, ; 4-4
"'\\''"  rune 0-4, ; 4-4
"'\\377'"  rune 0-6, ; 6-6
"'\\xff'"  rune 0-6, ; 6-6
"'\\u12e4'"  rune 0-8, ; 8-8
"'\\U0001f600'"  rune 0-12, ; 12-12
"'가'"  rune 0-5, ; 5-5
"\"\""  string 0-2, ; 2-2
"\"a\\\"b\\n\""  string 0-8, ; 8-8
"``"  string 0-2, ; 2-2
"\"\\377\\xff\\u12e4\\U0001f600\""  string 0-26, ; 26-26
"`a\nb`"  string 0-5, ; 5-5
"08i"  imaginary 0-3, ; 3-3
"0_8i"  imaginary 0-4, ; 4-4
"08.0"  float 0-4, ; 4-4
"08e1"  float 0-4, ; 4-4
"0x1.p0"  float 0-6, ; 6-6
"0x_1p0"  float 0-6, ; 6-6
"'\\uD7FF'"  rune 0-8, ; 8-8
"'\\uE000'"  rune 0-8, ; 8-8
"\"\\U0010FFFF\""  string 0-12, ; 12-12
-/
#guard_msgs in
#eval show IO Unit from do
  for text in ["0", "42", "1_000", "0600", "0o600", "0b_1010", "0B1", "0O7", "0xBadFace",
      "0X_67_7a", "0.", ".25", "72.40", "1e9", "1E-6", "1_5.2e+3", "0x1p-2", "0x_1FFFp-16",
      "0x.1p4", "0i", "2.71828i", "1e6i", "0x1p-2i", "'a'", "'\\n'", "'\\''", "'\\377'",
      "'\\xff'", "'\\u12e4'", "'\\U0001f600'", "'가'", "\"\"", "\"a\\\"b\\n\"", "``",
      "\"\\377\\xff\\u12e4\\U0001f600\"", "`a\nb`",
      -- Longest match: a leading zero is octal only for integers without a fraction or exponent.
      "08i", "0_8i", "08.0", "08e1", "0x1.p0", "0x_1p0", "'\\uD7FF'", "'\\uE000'", "\"\\U0010FFFF\""] do
    IO.println s!"{repr text}  {showTokens text}"

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

-- Malformed input is an error at the offending character. A malformed literal must not fall back
-- to a shorter valid token, such as `.5e+` lexing as `.5e`, which would move the error.
/--
info: "0x"  1:3: hexadecimal literal has no digits
"0b2"  1:3: expected binary digit
"0B2"  1:3: expected binary digit
"1_"  1:3: expected any element
"0x1.5"  1:6: hexadecimal mantissa requires a 'p' exponent
"\"a"  1:3: expected any element
"\"a\nb\""  2:1: newline in string literal
"`a"  1:3: expected any element
"'ab'"  1:3: expected closing '
"''"  1:3: empty or unterminated rune literal
"'\\q'"  1:4: unknown escape sequence: \q
"'\\x1'"  1:5: satisfy: predicate not satisfied
"/* unterminated"  1:16: expected any element
"#"  1:1: unexpected character '#'
"0o8"  1:3: expected octal digit
"1e"  1:3: expected any element
"1e+"  1:4: expected any element
".5e-"  1:5: expected any element
".5_"  1:4: expected any element
"0x1p"  1:5: expected any element
"0xp1"  1:3: hexadecimal literal has no digits
"0x.p1"  1:4: hexadecimal literal has no digits
"0x_.1p0"  1:4: expected hexadecimal digit after '_'
"0b102"  1:5: invalid digit, radix point, or exponent for literal base
"0o78"  1:4: invalid digit, radix point, or exponent for literal base
"08"  1:3: invalid digit in octal literal
"0b1.0"  1:4: invalid digit, radix point, or exponent for literal base
"0o1e2"  1:4: invalid digit, radix point, or exponent for literal base
"1p2"  1:2: exponent marker does not match the literal base
"'\\400'"  1:6: octal escape exceeds 255
"\"\\777\""  1:6: octal escape exceeds 255
"'\\uD800'"  1:8: escape is not a Unicode scalar value
"\"\\U00110000\""  1:12: escape is not a Unicode scalar value
"😀"  1:1: unexpected character '😀'
"²"  1:1: unexpected character '²'
"١x"  1:1: unexpected character '١'
"á"  1:2: unexpected character '́'
"x y"  1:2: unexpected character ' '
"1__2"  1:3: satisfy: predicate not satisfied
"0x1__2"  1:5: satisfy: predicate not satisfied
"0b1_2"  1:5: expected binary digit
"0_8"  1:4: invalid digit in octal literal
"0x_"  1:4: expected hexadecimal digit after '_'
"0x1p_2"  1:5: satisfy: predicate not satisfied
".5e+"  1:5: expected any element
"x﻿"  1:2: unexpected character '﻿'
-/
#guard_msgs in
#eval show IO Unit from do
  for text in ["0x", "0b2", "0B2", "1_", "0x1.5", "\"a", "\"a\nb\"", "`a", "'ab'", "''", "'\\q'",
      "'\\x1'", "/* unterminated", "#", "0o8", "1e", "1e+", ".5e-", ".5_", "0x1p", "0xp1", "0x.p1",
      "0x_.1p0", "0b102", "0o78", "08", "0b1.0", "0o1e2", "1p2", "'\\400'", "\"\\777\"", "'\\uD800'",
      "\"\\U00110000\"", "😀", "²", "١x", "a\u0301", "x\u00a0y", "1__2", "0x1__2", "0b1_2", "0_8",
      "0x_", "0x1p_2", ".5e+", "x\uFEFF"] do
    IO.println s!"{repr text}  {(lexError text).getD "lexed"}"

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
