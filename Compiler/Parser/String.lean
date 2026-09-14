module

public import Compiler.Parser.Parser

public section

namespace Parser

/-- `pos` is the UTF-8 byte offset, which feeds `Span` directly.
Adapted from Std.Internal.Parsec.String. -/
instance : Iterator (Sigma String.Pos) Char String.Pos.Raw where
  pos it := it.2.offset
  hasNext it := ¬it.2.IsAtEnd
  next' it h := ⟨it.1, it.2.next (by simpa using h)⟩
  cur' it h := it.2.get (by simpa using h)

abbrev StringParse (α : Type) : Type := Parse (Sigma String.Pos) α

/--
Returns the current UTF-8 byte offset without consuming input.

Example: after `skipStr "가"` on `"가a"`, `offset` returns `3`.
-/
def offset : StringParse Nat := fun it => .ok it it.2.offset.byteIdx

/--
Consumes `s` when the remaining input starts with it, and fails otherwise.

Example: `skipStr "ab"` on `"abc"` leaves `"c"`. On `"ac"` it fails with `expected 'ab'`.
-/
def skipStr (s : String) : StringParse Unit := fun it =>
  if (it.1.sliceFrom it.2).startsWith s then
    .ok ⟨it.1, it.2.nextn s.length⟩ ()
  else
    .err it (.other s!"expected '{s}'")

/--
Reports whether the next character satisfies `pred`, without consuming input.

Example: `peekIs (· == 'a')` on `"ab"` returns `true`. At end of input it returns `false`.
-/
@[inline]
def peekIs (pred : Char → Bool) : StringParse Bool := fun it =>
  if h : ¬it.2.IsAtEnd then .ok it (pred (it.2.get h)) else .ok it false

/--
Consumes the next character when it satisfies `pred`, reporting whether it was there.

Example: `skipIf (· == 'a')` on `"ab"` returns `true` and leaves `"b"`.
On `"ba"` it returns `false` and leaves `"ba"`.
-/
@[inline]
def skipIf (pred : Char → Bool) : StringParse Bool := fun it =>
  if h : ¬it.2.IsAtEnd then
    if pred (it.2.get h) then .ok ⟨it.1, it.2.next h⟩ true else .ok it false
  else
    .ok it false

/--
Consumes the character `c`, failing with `expected {what}` when it is absent.

Example: `expect '\'' "closing '"` on `"'x"` leaves `"x"`. On `"x"` it fails with `expected closing '`.
-/
def expect (c : Char) (what : String) : StringParse Unit := do
  unless (← skipIf (· == c)) do fail s!"expected {what}"

@[specialize]
private def skipWhilePos {s : String} (pos : s.Pos) (pred : Char → Bool) : s.Pos :=
  if h : ¬pos.IsAtEnd then
    if pred (pos.get h) then skipWhilePos (pos.next h) pred else pos
  else
    pos
termination_by pos

/--
Discards characters while they satisfy `pred`, without allocating an array of them.

Example: `skipWhile Char.isDigit` on `"12ab"` leaves `"ab"`.
-/
@[inline]
def skipWhile (pred : Char → Bool) : StringParse Unit := fun it =>
  .ok ⟨it.1, skipWhilePos it.2 pred⟩ ()

end Parser
