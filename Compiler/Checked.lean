module

public import Compiler.IR

public section

namespace GoAot.Checked

/-- Index into a function's `locals` array. Parameter IDs come first. -/
abbrev LocalId := Nat
/-- Source order index into `File.functions`. -/
abbrev FunctionId := Nat

inductive Expr where
  | intLiteral (value : Int)
  | floatLiteral (value : Float)
  | boolLiteral (value : Bool)
  | local (id : LocalId)
  | call (function : FunctionId) (arguments : Array Expr)
  | binary (op : IR.Op) (ty : Ty) (left right : Expr)
  | shift (op : IR.ShiftOp) (ty : Ty) (value : Expr) (countTy : Ty) (count : Expr)
  | convert (source target : Ty) (value : Expr)
  /-- Short circuit conjunction. `right` runs only when `left` is true. -/
  | and (left right : Expr)
  /-- Short circuit disjunction. `right` runs only when `left` is false. -/
  | or (left right : Expr)

inductive Stmt where
  | declare (id : LocalId) (initializer : Expr)
  | assign (id : LocalId) (value : Expr)
  | printString (bytes : ByteArray)
  | print (ty : Ty) (value : Expr)
  | callVoid (function : FunctionId) (arguments : Array Expr)
  /-- Evaluates a value-returning call and drops its result. -/
  | discard (value : Expr)
  | return (value : Option Expr)
  | ifThen (condition : Expr) (body : Array Stmt) (elseBody : Option (Array Stmt))
  | forLoop (initializer : Option Stmt) (condition : Option Expr) (post : Option Stmt)
      (body : Array Stmt)
  | break
  | continue

structure Function where
  name : String
  parameters : Array IR.Parameter
  /-- Slot types indexed by `LocalId`, including parameters and declarations in dead source. -/
  locals : Array Ty
  returnKind : IR.ReturnKind
  body : Array Stmt

structure File where
  functions : Array Function

end GoAot.Checked
