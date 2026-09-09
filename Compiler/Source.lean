module

public section

namespace GoAot

/-- Physical source position: zero-based UTF-8 offset, one-based line and byte column. -/
structure Position where
  offset : Nat
  line : Nat
  column : Nat
  deriving Repr, BEq

/-- Half-open UTF-8 byte range in the original source. -/
structure Span where
  start : Nat
  stop : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure Source where
  text : String
  private lineStarts : Array Nat

def Source.ofString (text : String) : Source := Id.run do
  let bytes := text.toUTF8
  let mut starts := #[0]
  for i in [:bytes.size] do
    if bytes[i]! == 10 then
      starts := starts.push (i + 1)
  return ⟨text, starts⟩

private def upperBound (values : Array Nat) (target : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := values.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if values[mid]! <= target then lo := mid + 1 else hi := mid
  return lo

/-- Offset of the first newline in `[start, stop)`, if any. -/
def Source.firstNewline? (source : Source) (start stop : Nat) : Option Nat :=
  match source.lineStarts[upperBound source.lineStarts start]? with
  | some nextLineStart =>
    if nextLineStart <= stop then some (nextLineStart - 1) else none
  | none => none

/-- Returns none for offsets past EOF. EOF itself is a valid position. -/
def Source.position? (source : Source) (offset : Nat) : Option Position := do
  if offset > source.text.utf8ByteSize then none else do
    let starts := source.lineStarts
    let i := upperBound starts offset - 1
    return ⟨offset, i + 1, offset - starts[i]! + 1⟩

end GoAot
