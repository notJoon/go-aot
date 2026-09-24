module

public import Compiler.Types

public section

namespace GoAot.IR

abbrev ValueId := Nat

/-- Identifies a mutable stack slot within a function, independently of value IDs. -/
abbrev SlotId := Nat

/-- Literals take their type from the instruction that uses them. -/
inductive Operand where
  | value (id : ValueId)
  /-- An integer that the using type must be able to represent. -/
  | literal (value : Int)
  /-- A finite float64. -/
  | floatLiteral (value : Float)
  | boolLiteral (value : Bool)
  | argument (index : Nat)
  deriving BEq

inductive Op where
  | add
  | subtract
  | multiply
  /-- Go division: panics on a zero divisor and wraps the most negative value divided by -1. -/
  | divide
  /-- Go remainder, with the sign of the dividend and the same zero and -1 rules as `divide`. -/
  | remainder
  | bitAnd
  | bitOr
  | bitXor
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

/-- Whether `op` is defined on operands of type `ty`. -/
def Op.accepts (op : Op) (ty : Ty) : Bool :=
  match op with
  | .equal | .notEqual => true
  | .add | .subtract | .multiply | .divide | .less | .lessEqual | .greater | .greaterEqual =>
    ty.isNumeric
  | .remainder | .bitAnd | .bitOr | .bitXor => ty.isInteger

/--
Go shifts. A count at or above the width yields 0, or -1 for `right` on a negative signed value.
-/
inductive ShiftOp where
  | left
  | right
  deriving BEq

abbrev BlockId := Nat

/--
An operation within a basic block.

Values are defined once per function and used only after their definition in the same block.
Slots are allocated in the entry block and can be accessed from every block.
-/
inductive Instruction where
  /-- Allocates a slot of the given type in the entry block. Does not initialize its contents. -/
  | alloca (slot : SlotId) (ty : Ty)
  /-- Reads a declared slot into a fresh value. `ty` must match the slot's declared type. -/
  | load (result : ValueId) (slot : SlotId) (ty : Ty)
  /-- Writes a value to a declared slot. Both `ty` and the operand must match its declared type. -/
  | store (slot : SlotId) (ty : Ty) (value : Operand)
  /-- Both operands have type `ty`, which `op` must accept. Comparisons produce a bool. -/
  | binary (result : ValueId) (op : Op) (ty : Ty) (left right : Operand)
  /-- Shifts an integer `value` of type `ty` by a `count` of any integer type `countTy`.
  A negative signed count panics. -/
  | shift (result : ValueId) (op : ShiftOp) (ty : Ty) (value : Operand) (countTy : Ty) (count : Operand)
  /-- Converts between numeric types. Integers truncate or extend by the source signedness. Floats
  convert to integers toward zero, saturating at the range of `target.floatConversionTy` with NaN
  as 0, then truncate to `target`. -/
  | convert (result : ValueId) (source target : Ty) (value : Operand)
  /-- Calls `name`, defining one value per callee result. -/
  | call (results : Array ValueId) (name : String) (arguments : Array Operand)
  -- Source escapes are decoded during checking, so the backend receives the final bytes.
  | printString (bytes : ByteArray)
  | print (ty : Ty) (value : Operand)

inductive Terminator where
  | br (target : BlockId)
  | condBr (condition : Operand) (ifTrue ifFalse : BlockId)
  /-- Returns one operand per function result. -/
  | ret (values : Array Operand)

structure Block where
  instructions : Array Instruction
  terminator : Terminator

structure Parameter where
  -- Display name only. Argument operands use indices, and lowering copies parameters into slots.
  name : String
  ty : Ty

structure Function where
  name : String
  parameters : Array Parameter
  /-- Result types. A function without results returns nothing, and `main` has none. -/
  results : Array Ty
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
