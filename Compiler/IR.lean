module

public import Compiler.Operator

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
  convert to integers toward zero, saturating at the range of `floatConversionTy target` with NaN
  as 0, then truncate to `target`. -/
  | convert (result : ValueId) (source target : Ty) (value : Operand)
  /-- Calls `name`, defining one value per callee result. -/
  | call (results : Array ValueId) (name : String) (arguments : Array Operand)
  -- Source escapes are decoded during checking, so the backend receives the final bytes.
  | printString (bytes : ByteArray)
  | print (ty : Ty) (value : Operand)

/--
The type a float converts through before truncating to `target`. Go leaves out-of-range float to
integer conversions to the implementation. Like gc on arm64, an integer narrower than 32 bits
saturates at 32 bits, so `uint8(300.0)` is 44 (#60).
-/
def floatConversionTy (target : Ty) : Ty :=
  if target.bits ≥ 32 then target else if target.isSigned then .int32 else .uint32

inductive Terminator where
  | br (target : BlockId)
  | condBr (condition : Operand) (ifTrue ifFalse : BlockId)
  /-- Returns one operand per function result. -/
  | ret (values : Array Operand)

structure Block where
  instructions : Array Instruction
  terminator : Terminator

structure Function where
  name : String
  parameters : Array Parameter
  /-- Result types. A function without results returns nothing, and `main` has none. -/
  results : Array Ty
  blocks : Array Block

structure Program where
  functions : Array Function

end GoAot.IR
