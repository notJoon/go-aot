module

public section

namespace GoAot.IR

abbrev ValueId := Nat

inductive Operand where
  | value (id : ValueId)
  | literal (value : Nat)
  | argument (index : Nat)
  deriving BEq

inductive ValueKind where
  | int
  | bool
  deriving BEq

inductive Op where
  | add
  | subtract
  | less

abbrev BlockId := Nat

inductive ReturnKind where
  | void
  | int
  deriving BEq

-- Values are defined once per function and used only after their definition in the same block.
-- Local variables will require relaxing the block-local rule to dominance checking.
inductive Instruction where
  | binary (result : ValueId) (op : Op) (left right : Operand)
  | call (result : ValueId) (name : String) (arguments : Array Operand)
  -- Source escapes are decoded during lowering so every backend receives identical bytes.
  | printString (bytes : ByteArray)
  | printInt (value : Operand)

inductive Terminator where
  | br (target : BlockId)
  | condBr (condition : Operand) (ifTrue ifFalse : BlockId)
  | ret (value : Option Operand)

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
