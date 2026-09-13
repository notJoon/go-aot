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

end Parser
