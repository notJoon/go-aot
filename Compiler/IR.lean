module

public section

namespace GoAot.IR

inductive IntExpr where
  | literal (value : Nat)
  | argument (index : Nat)
  | call (name : String) (arguments : Array IntExpr)
  | add (left right : IntExpr)
  | subtract (left right : IntExpr)

inductive BoolExpr where
  | less (left right : IntExpr)

abbrev BlockId := Nat

inductive ReturnKind where
  | void
  | int
  deriving BEq

inductive Instruction where
  -- Source escapes are decoded during lowering so every backend receives identical bytes.
  | printString (bytes : ByteArray)
  | printInt (value : IntExpr)

inductive Terminator where
  | br (target : BlockId)
  | condBr (condition : BoolExpr) (ifTrue ifFalse : BlockId)
  | ret (value : Option IntExpr)

structure Block where
  instructions : Array Instruction
  terminator : Terminator

structure Function where
  name : String
  -- Display names only; expression references are resolved argument indices.
  parameters : Array String
  returnKind : ReturnKind
  blocks : Array Block

structure Program where
  functions : Array Function

private def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def validName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => (asciiLetter first || first == '_') &&
      rest.all fun c => asciiLetter c || asciiDigit c || c == '_'

end GoAot.IR
