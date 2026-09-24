module

public section

namespace GoAot

/--
A Go value type. `int` and `uint` are 64 bits wide, like on every 64 bit Go target, but remain
distinct from `int64` and `uint64` because Go requires explicit conversions between them.
-/
inductive Ty where
  | bool
  | int | int8 | int16 | int32 | int64
  | uint | uint8 | uint16 | uint32 | uint64
  | float64
  deriving BEq, Repr, Inhabited

namespace Ty

inductive Kind where
  | bool
  | signed
  | unsigned
  | float
  deriving BEq

def kind : Ty → Kind
  | .bool => .bool
  | .int | .int8 | .int16 | .int32 | .int64 => .signed
  | .uint | .uint8 | .uint16 | .uint32 | .uint64 => .unsigned
  | .float64 => .float

/-- Size in bytes, as Go's `unsafe.Sizeof` reports it. -/
def size : Ty → Nat
  | .bool | .int8 | .uint8 => 1
  | .int16 | .uint16 => 2
  | .int32 | .uint32 => 4
  | .int | .int64 | .uint | .uint64 | .float64 => 8

/-- Scalars are aligned to their size. -/
def align (ty : Ty) : Nat := ty.size

def bits (ty : Ty) : Nat := ty.size * 8

def isInteger (ty : Ty) : Bool := ty.kind == .signed || ty.kind == .unsigned

def isNumeric (ty : Ty) : Bool := ty.isInteger || ty.kind == .float

def isSigned (ty : Ty) : Bool := ty.kind == .signed

-- Literal bounds are closed terms that Lean computes once, so range checks do not allocate.
/-- The smallest value of an integer type, or 0 otherwise. Example: `Ty.int8.minValue = -128`. -/
def minValue : Ty → Int
  | .int8 => -128 | .int16 => -32768 | .int32 => -2147483648
  | .int | .int64 => -9223372036854775808
  | _ => 0

/-- The largest value of an integer type, or 0 otherwise. Example: `Ty.uint8.maxValue = 255`. -/
def maxValue : Ty → Int
  | .int8 => 127 | .int16 => 32767 | .int32 => 2147483647
  | .int | .int64 => 9223372036854775807
  | .uint8 => 255 | .uint16 => 65535 | .uint32 => 4294967295
  | .uint | .uint64 => 18446744073709551615
  | .bool | .float64 => 0

/-- Whether an integer type can represent `value`. -/
def contains (ty : Ty) (value : Int) : Bool :=
  ty.isInteger && ty.minValue ≤ value && value ≤ ty.maxValue

/--
The type a float converts through before truncating to `ty`. Like gc, a float converts to an
integer narrower than 32 bits by saturating at 32 bits, so `uint8(300.0)` is 44.
-/
def floatConversionTy (ty : Ty) : Ty :=
  if ty.bits ≥ 32 then ty else if ty.isSigned then .int32 else .uint32

def name : Ty → String
  | .bool => "bool"
  | .int => "int" | .int8 => "int8" | .int16 => "int16" | .int32 => "int32" | .int64 => "int64"
  | .uint => "uint" | .uint8 => "uint8" | .uint16 => "uint16" | .uint32 => "uint32"
  | .uint64 => "uint64"
  | .float64 => "float64"

def all : List Ty :=
  [.bool, .int, .int8, .int16, .int32, .int64, .uint, .uint8, .uint16, .uint32, .uint64, .float64]

/-- Resolve a predeclared type name. Example: `Ty.ofName? "uint16" = some .uint16`. -/
def ofName? (name : String) : Option Ty :=
  all.find? (·.name == name)

#guard all.all fun ty => !ty.isInteger ||
  (ty.minValue == (if ty.isSigned then -((2 ^ (ty.bits - 1) : Nat) : Int) else 0) &&
    ty.maxValue == (if ty.isSigned then 2 ^ (ty.bits - 1) - 1 else 2 ^ ty.bits - 1 : Nat))

end Ty

end GoAot
