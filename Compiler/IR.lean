module

public section

namespace GoAot.IR

inductive BinaryOp where
  | add | subtract | less

inductive Expr where
  | intLiteral (value : Nat)
  | local (name : String)
  | call (name : String) (arguments : Array Expr)
  | binary (op : BinaryOp) (left right : Expr)

inductive Instruction where
  -- Source escapes are decoded during lowering so every backend receives identical bytes.
  | printString (bytes : ByteArray)
  | printInt (value : Expr)
  | return (value : Expr)
  | ifThen (condition : Expr) (body : Array Instruction)

structure Function where
  name : String
  parameters : Array String
  body : Array Instruction

structure Program where
  functions : Array Function

end GoAot.IR
