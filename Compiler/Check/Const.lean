module

public import Compiler.Checked
public import Compiler.Diagnostic
public import Compiler.Syntax
import Compiler.Literal

/-!
Go constants for the checker: exact untyped values, their conversion to typed literals, and
constant folding.
-/

public section

namespace GoAot.Check

def diagnosticAt (span : Span) (message : String) : Diagnostic :=
  ⟨.check, some span, message⟩

/--
A checked operand. Untyped constants are exact, like Go's, and stay untyped until their context
gives them a type. A float constant rounds to float64 only then, so `0.1 + 0.2` is `0.3`.
-/
inductive Value where
  | int (value : Int)
  | float (value : Rat)
  | typed (expr : Checked.Expr) (ty : Ty)

def Value.isConst : Value → Bool
  | .typed .. => false
  | _ => true

def Value.typeName : Value → String
  | .int _ => "untyped int"
  | .float _ => "untyped float"
  | .typed _ ty => ty.name

/-- The type of a typed value, or the type a constant takes when its context has none. -/
def Value.defaultTy : Value → Ty
  | .int _ => .int
  | .float _ => .float64
  | .typed _ ty => ty

def Value.toRat : Value → Rat
  | .int value => value
  | .float value => value
  | .typed .. => 0

def Value.render : Value → String
  | .int value => toString value
  | .float value =>
    -- Lean prints six fractional digits, which the trailing zero trim shortens to Go's spelling.
    let text := toString (Literal.toFloat value)
    if text.contains '.' then ((text.dropEndWhile '0').dropEndWhile '.').copy else text
  | .typed _ ty => ty.name

def zeroValue (ty : Ty) : Checked.Expr :=
  match ty.kind with
  | .bool => .boolLiteral false
  | .float => .floatLiteral 0
  | .signed | .unsigned => .intLiteral 0

/-- The value with every bit set, used for `^x` and `x &^ y`. -/
def allOnes (ty : Ty) : Checked.Expr :=
  .intLiteral (if ty.isSigned then -1 else ty.maxValue)

def constInteger (value : Value) (span : Span) (target : String) : Except Diagnostic Int :=
  match value with
  | .int integer => pure integer
  | .typed .. => throw (diagnosticAt span "internal error: expected a constant")
  | .float exact =>
    if exact.den != 1 then throw (diagnosticAt span s!"constant {value.render} truncated to {target}")
    else pure exact.num

def floatTo (exact : Rat) (span : Span) : Except Diagnostic Checked.Expr := do
  let float := Literal.toFloat exact
  unless float.isFinite do throw (diagnosticAt span "constant overflows float64")
  return .floatLiteral float

def intTo (integer : Int) (ty : Ty) (span : Span) : Except Diagnostic Checked.Expr := do
  if ty.kind == .float then return ← floatTo integer span
  unless ty.contains integer do throw (diagnosticAt span s!"constant {integer} overflows {ty.name}")
  return .intLiteral integer

/--
Represent a constant as the numeric type `ty`, as an assignment or an explicit conversion does.
Every numeric type accepts a numeric constant unless the value overflows or truncates.
-/
def constTo (value : Value) (ty : Ty) (span : Span) : Except Diagnostic Checked.Expr := do
  match value, ty.kind with
  | .typed expr _, _ => return expr
  | .int integer, _ => intTo integer ty span
  | .float exact, .float => floatTo exact span
  | .float _, _ => intTo (← constInteger value span ty.name) ty span

/-- Apply a bitwise `Nat` operation to integers in two's complement. -/
def bitwise (op : Nat → Nat → Nat) (left right : Int) : Int :=
  let width := (max left.natAbs right.natAbs).log2 + 2
  let modulus : Int := (2 ^ width : Nat)
  let result : Int := (op (left % modulus).toNat (right % modulus).toNat : Nat)
  if result ≥ modulus / 2 then result - modulus else result

/-- Fold an operator the operands' default types accept. Comparisons produce a typed bool. -/
def foldConst (op : Syntax.BinaryOp) (left right : Value) (rightSpan : Span) :
    Except Diagnostic Value := do
  let divisionByZero := diagnosticAt rightSpan "division by zero"
  let compare (ordering : Ordering) : Value :=
    .typed (.boolLiteral (match op with
      | .equal => ordering == .eq | .notEqual => ordering != .eq
      | .less => ordering == .lt | .lessEqual => ordering != .gt
      | .greater => ordering == .gt | _ => ordering != .lt)) .bool
  match left, right with
  | .int a, .int b =>
    match op with
    | .add => return .int (a + b)
    | .subtract => return .int (a - b)
    | .multiply => return .int (a * b)
    | .divide => if b == 0 then throw divisionByZero else return .int (a.tdiv b)
    | .remainder => if b == 0 then throw divisionByZero else return .int (a.tmod b)
    | .bitAnd => return .int (bitwise (· &&& ·) a b)
    | .bitOr => return .int (bitwise (· ||| ·) a b)
    | .bitXor => return .int (bitwise (· ^^^ ·) a b)
    | .bitClear => return .int (bitwise (· &&& ·) a (-b - 1))
    | _ => return compare (compareOfLessAndEq a b)
  | _, _ =>
    let a := left.toRat
    let b := right.toRat
    match op with
    | .add => return .float (a + b)
    | .subtract => return .float (a - b)
    | .multiply => return .float (a * b)
    | .divide => if b == 0 then throw divisionByZero else return .float (a / b)
    | _ => return compare (if a < b then .lt else if a == b then .eq else .gt)

end GoAot.Check
