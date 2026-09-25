module

public import Compiler.Operator

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
  | binary (op : Op) (ty : Ty) (left right : Expr)
  | shift (op : ShiftOp) (ty : Ty) (value : Expr) (countTy : Ty) (count : Expr)
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
  /-- Calls a function for its effects, dropping any results. -/
  | call (function : FunctionId) (arguments : Array Expr)
  /-- Stores each result of a call in its local, or drops the result for `none`. -/
  | callAssign (targets : Array (Option LocalId)) (function : FunctionId) (arguments : Array Expr)
  | return (values : Array Expr)
  /-- Returns every result of a call, as `return f()` does for a function with several results. -/
  | returnCall (function : FunctionId) (arguments : Array Expr)
  | ifThen (condition : Expr) (body : Array Stmt) (elseBody : Option (Array Stmt))
  | forLoop (initializer : Option Stmt) (condition : Option Expr) (post : Option Stmt)
      (body : Array Stmt)
  | break
  | continue

structure Function where
  name : String
  parameters : Array Parameter
  /-- Slot types indexed by `LocalId`, including parameters and declarations in dead source. -/
  locals : Array Ty
  results : Array Ty
  body : Array Stmt

structure File where
  functions : Array Function

end GoAot.Checked
