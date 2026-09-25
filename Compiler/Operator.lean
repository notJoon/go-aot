module

public import Compiler.Types

public section

namespace GoAot

/-!
Operators and signatures that the checked tree and the IR share, so neither depends on the other.
-/

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

/-- A named function parameter. -/
structure Parameter where
  -- Display name only. IR argument operands use indices, and lowering copies parameters into slots.
  name : String
  ty : Ty

end GoAot
