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

inductive Instruction where
  -- Source escapes are decoded during lowering so every backend receives identical bytes.
  | printString (bytes : ByteArray)
  | printInt (value : IntExpr)
  | return (value : IntExpr)
  | ifThen (condition : BoolExpr) (body : Array Instruction)

structure Function where
  name : String
  -- Display names only; expression references are resolved argument indices.
  parameters : Array String
  body : Array Instruction

structure Program where
  -- Producers must satisfy Lowering's name, arity, literal-range, and return checks.
  functions : Array Function

end GoAot.IR
