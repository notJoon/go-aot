module

public section

namespace GoAot.IR

def maxSignedInt64 : Nat := 9223372036854775807

abbrev ValueId := Nat

/-- Identifies a mutable stack slot within a function, independently of value IDs. -/
abbrev SlotId := Nat

inductive Operand where
  | value (id : ValueId)
  | literal (value : Nat)
  | boolLiteral (value : Bool)
  | argument (index : Nat)
  deriving BEq

inductive ValueKind where
  | int
  | bool
  deriving BEq

/-- The Go spelling of a value kind, used in diagnostics. -/
def ValueKind.name : ValueKind → String
  | .int => "int"
  | .bool => "bool"

inductive Op where
  | add
  | subtract
  | multiply
  /-- Go division: panics on a zero divisor and wraps the most negative value divided by -1. -/
  | divide
  /-- Go remainder, with the sign of the dividend and the same zero and -1 rules as `divide`. -/
  | remainder
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving BEq

def Op.isComparison : Op → Bool
  | .equal | .notEqual | .less | .lessEqual | .greater | .greaterEqual => true
  | _ => false

abbrev BlockId := Nat

inductive ReturnKind where
  | void
  | value (kind : ValueKind)
  deriving BEq

/--
An operation within a basic block.

Values are defined once per function and used only after their definition in the same block.
Slots are allocated in the entry block and can be accessed from every block.
-/
inductive Instruction where
  /-- Allocates a slot of the given kind in the entry block. Does not initialize its contents. -/
  | alloca (slot : SlotId) (kind : ValueKind)
  /-- Reads a declared slot into a fresh value. `kind` must match the slot's declared kind. -/
  | load (result : ValueId) (slot : SlotId) (kind : ValueKind)
  /-- Writes a value to a declared slot. Both `kind` and the operand must match its declared kind. -/
  | store (slot : SlotId) (kind : ValueKind) (value : Operand)
  /-- Both operands have kind `kind`. Only `equal` and `notEqual` accept bool operands. -/
  | binary (result : ValueId) (op : Op) (kind : ValueKind) (left right : Operand)
  | call (result : ValueId) (name : String) (arguments : Array Operand)
  | callVoid (name : String) (arguments : Array Operand)
  -- Source escapes are decoded during checking so every backend receives identical bytes.
  | printString (bytes : ByteArray)
  | printInt (value : Operand)

inductive Terminator where
  | br (target : BlockId)
  | condBr (condition : Operand) (ifTrue ifFalse : BlockId)
  | ret (value : Option Operand)

structure Block where
  instructions : Array Instruction
  terminator : Terminator

structure Parameter where
  -- Display name only. Argument operands use indices, and lowering copies parameters into slots.
  name : String
  kind : ValueKind

structure Function where
  name : String
  parameters : Array Parameter
  returnKind : ReturnKind
  blocks : Array Block

structure Program where
  functions : Array Function

private def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def validName (name : String) : Bool :=
  !name.isEmpty && (asciiLetter name.front || name.front == '_') &&
    name.all fun c => asciiLetter c || asciiDigit c || c == '_'

end GoAot.IR
