module

public import Compiler.IR

public section

namespace GoAot.Checked

/-- Index into a function's `locals` array. Parameter IDs come first. -/
abbrev LocalId := Nat
/-- Source order index into `File.functions`. -/
abbrev FunctionId := Nat

inductive Expr where
  | intLiteral (value : Nat)
  | local (id : LocalId)
  | call (function : FunctionId) (arguments : Array Expr)
  | binary (op : IR.Op) (left right : Expr)

inductive Stmt where
  | declare (id : LocalId) (initializer : Expr)
  | assign (id : LocalId) (value : Expr)
  | printString (bytes : ByteArray)
  | printInt (value : Expr)
  | callVoid (function : FunctionId) (arguments : Array Expr)
  | return (value : Option Expr)
  | ifThen (condition : Expr) (body : Array Stmt) (elseBody : Option (Array Stmt))
  | forLoop (initializer : Option Stmt) (condition : Option Expr) (post : Option Stmt)
      (body : Array Stmt)
  | break
  | continue

structure Function where
  name : String
  parameters : Array String
  /-- Slot kinds indexed by `LocalId`, including parameters and declarations in dead source. -/
  locals : Array IR.ValueKind
  returnKind : IR.ReturnKind
  body : Array Stmt

structure File where
  functions : Array Function

end GoAot.Checked
