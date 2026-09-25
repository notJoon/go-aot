module

public import Compiler.Checked
public import Compiler.Scope
public import Compiler.Syntax
import Compiler.Literal
import Std.Data.HashMap

public section

namespace GoAot.Check

private def diagnosticAt (span : Span) (message : String) : Diagnostic :=
  ⟨.check, some span, message⟩

private structure Signature where
  id : Checked.FunctionId
  name : String
  parameters : Array IR.Parameter
  results : Array Ty
  -- Retain parameter bindings for lookup and duplicate declarations in the body.
  scope : Scope

-- Type names are compared by spelling, so they cannot be shadowed yet.
private def resolveType (typeName : Syntax.Ident) : Except Diagnostic Ty :=
  match Ty.ofName? typeName.text.copy with
  | some ty => pure ty
  | none => throw (diagnosticAt typeName.span s!"unsupported type '{typeName.text}'")

private def signatures (file : Syntax.File) : Except Diagnostic (Std.HashMap String Signature) := do
  let mut result : Std.HashMap String Signature := {}
  for h : i in [:file.functions.size] do
    let function := file.functions[i]
    let name := function.name.text.copy
    if result.contains name then
      throw (diagnosticAt function.name.span s!"duplicate function '{name}'")
    let mut parameters := #[]
    let mut scope := Scope.empty
    for parameter in function.parameters do
      let ty ← resolveType parameter.typeName
      let parameterName := parameter.name.text.copy
      scope ← scope.declare parameterName
        ⟨.parameter, parameters.size, ty, parameter.name.span⟩
      parameters := parameters.push ⟨parameterName, ty⟩
    let results ← function.results.mapM resolveType
    result := result.insert name ⟨i, name, parameters, results, scope⟩
  return result

private structure Context where
  all : Std.HashMap String Signature
  signature : Signature
  scope : Scope
  loopDepth : Nat := 0

private abbrev CheckM := ReaderT Context (StateT (Array Ty) (Except Diagnostic))

-- Expressions only read bindings. Keeping local allocation state out avoids a result/state pair
-- for every recursive operand check.
private abbrev ExprM := ReaderT Context (Except Diagnostic)

@[inline] private def withScope (scope : Scope) (action : CheckM α) : CheckM α :=
  withReader (fun context => { context with scope }) action

private def checkCallable (scope : Scope) (name : String) (span : Span) : Except Diagnostic Unit := do
  if (scope.find? name).isSome then
    throw (diagnosticAt span s!"cannot call non-function '{name}'")

/--
A checked operand. Untyped constants are exact, like Go's, and stay untyped until their context
gives them a type. A float constant rounds to float64 only then, so `0.1 + 0.2` is `0.3`.
-/
private inductive Value where
  | int (value : Int)
  | float (value : Rat)
  | typed (expr : Checked.Expr) (ty : Ty)

private def Value.isConst : Value → Bool
  | .typed .. => false
  | _ => true

private def Value.typeName : Value → String
  | .int _ => "untyped int"
  | .float _ => "untyped float"
  | .typed _ ty => ty.name

/-- The type of a typed value, or the type a constant takes when its context has none. -/
private def Value.defaultTy : Value → Ty
  | .int _ => .int
  | .float _ => .float64
  | .typed _ ty => ty

private def Value.toRat : Value → Rat
  | .int value => value
  | .float value => value
  | .typed .. => 0

private def Value.render : Value → String
  | .int value => toString value
  | .float value =>
    -- Lean prints six fractional digits, which the trailing zero trim shortens to Go's spelling.
    let text := toString (Literal.toFloat value)
    if text.contains '.' then ((text.dropEndWhile '0').dropEndWhile '.').copy else text
  | .typed _ ty => ty.name

private def zeroValue (ty : Ty) : Checked.Expr :=
  match ty.kind with
  | .bool => .boolLiteral false
  | .float => .floatLiteral 0
  | .signed | .unsigned => .intLiteral 0

/-- The value with every bit set, used for `^x` and `x &^ y`. -/
private def allOnes (ty : Ty) : Checked.Expr :=
  .intLiteral (if ty.isSigned then -1 else ty.maxValue)

private def constInteger (value : Value) (span : Span) (target : String) : Except Diagnostic Int :=
  match value with
  | .int integer => pure integer
  | .typed .. => throw (diagnosticAt span "internal error: expected a constant")
  | .float exact =>
    if exact.den != 1 then throw (diagnosticAt span s!"constant {value.render} truncated to {target}")
    else pure exact.num

private def floatTo (exact : Rat) (span : Span) : Except Diagnostic Checked.Expr := do
  let float := Literal.toFloat exact
  unless float.isFinite do throw (diagnosticAt span "constant overflows float64")
  return .floatLiteral float

private def intTo (integer : Int) (ty : Ty) (span : Span) : Except Diagnostic Checked.Expr := do
  if ty.kind == .float then return ← floatTo integer span
  unless ty.contains integer do throw (diagnosticAt span s!"constant {integer} overflows {ty.name}")
  return .intLiteral integer

/--
Represent a constant as the numeric type `ty`, as an assignment or an explicit conversion does.
Every numeric type accepts a numeric constant unless the value overflows or truncates.
-/
private def constTo (value : Value) (ty : Ty) (span : Span) : Except Diagnostic Checked.Expr := do
  match value, ty.kind with
  | .typed expr _, _ => return expr
  | .int integer, _ => intTo integer ty span
  | .float exact, .float => floatTo exact span
  | .float _, _ => intTo (← constInteger value span ty.name) ty span

/-- Apply a bitwise `Nat` operation to integers in two's complement. -/
private def bitwise (op : Nat → Nat → Nat) (left right : Int) : Int :=
  let width := (max left.natAbs right.natAbs).log2 + 2
  let modulus : Int := (2 ^ width : Nat)
  let result : Int := (op (left % modulus).toNat (right % modulus).toNat : Nat)
  if result ≥ modulus / 2 then result - modulus else result

private def irOp? : Syntax.BinaryOp → Option IR.Op
  | .add => some .add | .subtract => some .subtract | .multiply => some .multiply
  | .divide => some .divide | .remainder => some .remainder
  -- `x &^ y` lowers to `x & ^y`.
  | .bitAnd | .bitClear => some .bitAnd | .bitOr => some .bitOr | .bitXor => some .bitXor
  | .equal => some .equal | .notEqual => some .notEqual
  | .less => some .less | .lessEqual => some .lessEqual
  | .greater => some .greater | .greaterEqual => some .greaterEqual
  | .and | .or | .shiftLeft | .shiftRight => none

/-- Fold an operator the operands' default types accept. Comparisons produce a typed bool. -/
private def foldConst (op : Syntax.BinaryOp) (left right : Value) (rightSpan : Span) :
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

mutual
  private partial def checkValue (hint : Option Ty) : Syntax.Expr → ExprM Value
    | .intLiteral text _ => return .int (Literal.decodeInt text)
    | .floatLiteral text span =>
      match Literal.decodeFloat? text with
      | some value => return .float value
      | none => throw (diagnosticAt span "hexadecimal floating-point literals are unsupported")
    | .identifier name => do
      -- `true` and `false` are predeclared identifiers, so local bindings shadow them.
      match (← read).scope.find? name.text.copy with
      | some symbol => return .typed (.local symbol.id) symbol.ty
      | none =>
        if name.text == "true" then return .typed (.boolLiteral true) .bool
        if name.text == "false" then return .typed (.boolLiteral false) .bool
        throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
    | .call callee arguments span => do
      let name := callee.text.copy
      if let .error error := checkCallable (← read).scope name callee.span then throw error
      -- A package level function would shadow a predeclared type of the same name.
      match (← read).all[name]?, Ty.ofName? name with
      | some signature, _ =>
        match signature.results with
        | #[ty] => return .typed (.call signature.id (← checkArguments signature arguments span)) ty
        | #[] => throw (diagnosticAt callee.span s!"function '{callee.text}' does not return a value")
        | _ => throw (diagnosticAt callee.span s!"multiple-value {callee.text}() in single-value context")
      | none, some target => checkConversion target arguments span
      | none, none => throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
    | .binary op left right span => checkBinary hint op left right span
    | .unary op operand _ => do
      let value ← checkValue hint operand
      let notDefined : ExprM Value := throw (diagnosticAt operand.span
        s!"operator {match op with | .negate => "-" | .not => "!" | .complement => "^"} is not defined on {value.typeName}")
      -- Unary operators desugar to binary IR: `-x` is `0 - x`, or `x * -1.0` to keep the sign
      -- of a float zero, `!x` is `x == false`, and `^x` is `x ^ allOnes`.
      match op, value with
      | .negate, .int integer => return .int (-integer)
      | .negate, .float exact => return .float (-exact)
      | .negate, .typed expr ty =>
        match ty.kind with
        | .signed | .unsigned => return .typed (.binary .subtract ty (.intLiteral 0) expr) ty
        | .float => return .typed (.binary .multiply ty expr (.floatLiteral (-1))) ty
        | .bool => notDefined
      | .complement, .int integer => return .int (-integer - 1)
      | .complement, .typed expr ty =>
        if ty.isInteger then return .typed (.binary .bitXor ty expr (allOnes ty)) ty else notDefined
      | .not, .typed expr .bool => return .typed (.binary .equal .bool expr (.boolLiteral false)) .bool
      | _, _ => notDefined
    | .stringLiteral _ span => throw (diagnosticAt span "strings can only be printed")

  /-- Check an operand and give an untyped constant the `hint` type, or its default type. -/
  private partial def checkTyped (hint : Option Ty) (expr : Syntax.Expr) : ExprM (Checked.Expr × Ty) := do
    -- A non-numeric hint leaves the mismatch for the caller to report.
    let numericHint (default : Ty) := match hint with
      | some ty => if ty.isNumeric then ty else default
      | none => default
    -- Integer literals are the most common operand, so they skip the untyped `Value`.
    if let .intLiteral text span := expr then
      let ty := numericHint .int
      return (← intTo (Literal.decodeInt text) ty span, ty)
    match ← checkValue hint expr with
    | .typed checked ty => return (checked, ty)
    | value =>
      let ty := numericHint value.defaultTy
      return (← constTo value ty expr.span, ty)

  private partial def checkArguments (signature : Signature) (arguments : Array Syntax.Expr)
      (span : Span) : ExprM (Array Checked.Expr) := do
    if arguments.size != signature.parameters.size then
      throw (diagnosticAt span s!"function '{signature.name}' expects {signature.parameters.size} arguments")
    let mut checked := #[]
    for argument in arguments, parameter in signature.parameters do
      let (value, ty) ← checkTyped parameter.ty argument
      unless ty == parameter.ty do
        throw (diagnosticAt argument.span s!"function arguments must be {parameter.ty.name}")
      checked := checked.push value
    return checked

  private partial def checkConversion (target : Ty) (arguments : Array Syntax.Expr) (span : Span) :
      ExprM Value := do
    let #[argument] := arguments
      | throw (diagnosticAt span s!"conversion to {target.name} expects one argument")
    match ← checkValue target argument with
    | .typed checked ty =>
      if ty == target then return .typed checked ty
      unless ty.isNumeric && target.isNumeric do
        throw (diagnosticAt argument.span s!"cannot convert {ty.name} to {target.name}")
      return .typed (.convert ty target checked) target
    | value =>
      unless target.isNumeric do
        throw (diagnosticAt argument.span s!"cannot convert {value.typeName} to {target.name}")
      return .typed (← constTo value target argument.span) target

  private partial def checkBinary (hint : Option Ty) (op : Syntax.BinaryOp)
      (left right : Syntax.Expr) (span : Span) : ExprM Value := do
    match op, irOp? op with
    | .and, _ | .or, _ =>
      let (left', leftTy) ← checkTyped Ty.bool left
      unless leftTy == .bool do throw (diagnosticAt left.span "logical operands must be bool")
      let (right', rightTy) ← checkTyped Ty.bool right
      unless rightTy == .bool do throw (diagnosticAt right.span "logical operands must be bool")
      return .typed (if op == .and then .and left' right' else .or left' right') .bool
    | _, none => checkShift hint op left right span
    | _, some irOp =>
      -- Comparison results are bools, so their operands have no type from context.
      let operandHint := if irOp.isComparison then none else hint
      let leftValue ← checkValue operandHint left
      let rightValue ← checkValue operandHint right
      -- An operand whose type rejects the operator is reported where it appears. A constant
      -- takes the other operand's type, or with another constant the later kind of int, float.
      for (operand, value) in [(left, leftValue), (right, rightValue)] do
        if let .typed _ ty := value then
          unless irOp.accepts ty do
            throw (diagnosticAt operand.span s!"operator {op.symbol} is not defined on {ty.name}")
      if leftValue.isConst && rightValue.isConst then
        let float := leftValue matches .float _ || rightValue matches .float _
        unless irOp.accepts (if float then .float64 else .int) do
          throw (diagnosticAt span s!"operator {op.symbol} is not defined on untyped float")
      let mismatch := diagnosticAt right.span
        s!"mismatched types {leftValue.typeName} and {rightValue.typeName}"
      let (left', right', ty) ← match leftValue, rightValue with
        | .typed left' ty, .typed right' rightTy =>
          if ty != rightTy then throw mismatch
          pure (left', right', ty)
        | .typed left' ty, constant =>
          unless ty.isNumeric do throw mismatch
          pure (left', ← constTo constant ty right.span, ty)
        | constant, .typed right' ty =>
          unless ty.isNumeric do throw mismatch
          pure (← constTo constant ty left.span, right', ty)
        | a, b => return ← foldConst op a b right.span
      if irOp == .divide || irOp == .remainder then
        if right' matches .intLiteral 0 || right' matches .floatLiteral 0 then
          throw (diagnosticAt right.span "division by zero")
      let right' := if op == .bitClear then .binary .bitXor ty right' (allOnes ty) else right'
      return .typed (.binary irOp ty left' right') (if irOp.isComparison then .bool else ty)

  private partial def checkShift (hint : Option Ty) (op : Syntax.BinaryOp)
      (left right : Syntax.Expr) (span : Span) : ExprM Value := do
    let shift : IR.ShiftOp := if op == .shiftLeft then .left else .right
    let leftValue ← checkValue hint left
    let count ← checkValue none right
    let countValue? ← match count with
      | .typed _ ty =>
        unless ty.isInteger do throw (diagnosticAt right.span "shift count must be an integer")
        pure none
      | value =>
        let count ← constInteger value right.span "shift count"
        if count < 0 then throw (diagnosticAt right.span "negative shift count")
        pure (some count)
    match leftValue.isConst, countValue? with
    | true, some count =>
      let integer ← constInteger leftValue left.span "untyped int"
      if count > 1024 then throw (diagnosticAt right.span "shift count too large")
      return .int (if shift == .left then integer * 2 ^ count.toNat else integer.shiftRight count.toNat)
    | _, _ =>
      -- A constant shifted by a variable count takes the type of its context, or int.
      let (left', ty) ← match leftValue with
        | .typed left' ty => pure (left', ty)
        | value =>
          let ty := match hint with | some ty => if ty.isInteger then ty else .int | none => .int
          pure (← constTo value ty left.span, ty)
      unless ty.isInteger do
        throw (diagnosticAt left.span s!"operator {op.symbol} is not defined on {ty.name}")
      let (count', countTy) ← match count, countValue? with
        | .typed count' countTy, _ => pure (count', countTy)
        | _, some count =>
          unless Ty.uint64.contains count do throw (diagnosticAt right.span "shift count too large")
          pure (.intLiteral count, .uint64)
        | _, none => throw (diagnosticAt span "internal error: missing shift count")
      return .typed (.shift shift ty left' countTy count') ty
end

private def checkPrintln (callee : Syntax.Ident) (arguments : Array Syntax.Expr)
    (span : Span) : CheckM Checked.Stmt := do
  let name := callee.text.copy
  if let .error error := checkCallable (← read).scope name callee.span then throw error
  let #[argument] := arguments
    | throw (diagnosticAt span "println expects one argument")
  match argument with
  | .stringLiteral literal span =>
    if literal.startsWith "\"" then return .printString (Literal.decodeInterpreted literal)
    else throw (diagnosticAt span "raw string literals are not supported yet")
  | _ => do
    let (value, ty) ← (checkTyped none argument).run (← read)
    return .print ty value

private def checkDeclaration (name : Syntax.Ident) (typeName : Option Syntax.Ident)
    (initializer : Option Syntax.Expr) : CheckM (Checked.Stmt × Context) := do
  if typeName.isNone && initializer.isNone then
    throw (diagnosticAt name.span "variable declaration requires a type or initializer")
  let nameText := name.text.copy
  if nameText == "_" then
    throw (diagnosticAt name.span s!"unsupported local name '{nameText}'")
  let declared ← typeName.mapM fun typeName => (monadLift (resolveType typeName) : CheckM Ty)
  -- The initializer cannot see the binding being declared.
  let (value, ty) ← match initializer, declared with
    | some value, _ => (checkTyped declared value).run (← read)
    | none, some ty => pure (zeroValue ty, ty)
    | none, none => pure (zeroValue .int, .int)
  if let some declared := declared then
    if ty != declared then
      throw (diagnosticAt ((initializer.map (·.span)).getD name.span)
        s!"initializer must be {declared.name}")
  let id := (← get).size
  let context ← read
  let scope ← context.scope.declare nameText ⟨.local, id, ty, name.span⟩
  modify (·.push ty)
  return (.declare id value, { context with scope })

/--
Bind each result of a call to a name. `:=` declares names that are new in the current scope and
assigns the others, and needs at least one new name, as in Go.
-/
private def checkMultiAssignment (names : Array Syntax.Ident) (define : Bool) (value : Syntax.Expr) :
    CheckM (Checked.Stmt × Context) := do
  let context ← read
  let mismatch (values : String) :=
    diagnosticAt value.span s!"assignment mismatch: {names.size} variables but {values}"
  let .call callee arguments span := value | throw (mismatch "1 value")
  let plural (count : Nat) := if count == 1 then "1 value" else s!"{count} values"
  let name := callee.text.copy
  if let .error error := checkCallable context.scope name callee.span then throw error
  let some signature := context.all[name]?
    | if (Ty.ofName? name).isSome then throw (mismatch "1 value")
      else throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
  unless signature.results.size == names.size do
    throw (mismatch s!"{callee.text}() returns {plural signature.results.size}")
  let arguments ← (checkArguments signature arguments span).run context
  let mut scope := context.scope
  let mut targets := #[]
  let mut declared : Array String := #[]
  for target in names, ty in signature.results do
    let text := target.text.copy
    if text == "_" then
      targets := targets.push none
      continue
    if define && declared.contains text then
      throw (diagnosticAt target.span s!"'{text}' repeated on left side of :=")
    match if define then scope.findHere? text else scope.find? text with
    | some symbol =>
      unless symbol.ty == ty do
        throw (diagnosticAt target.span "assignment type does not match variable type")
      targets := targets.push (some symbol.id)
    | none =>
      unless define do throw (diagnosticAt target.span s!"unknown identifier '{text}'")
      let id := (← get).size
      scope ← scope.declare text ⟨.local, id, ty, target.span⟩
      modify (·.push ty)
      targets := targets.push (some id)
      declared := declared.push text
  if define && declared.isEmpty then
    throw (diagnosticAt ((names[0]?.map (·.span)).getD value.span) "no new variables on left side of :=")
  return (.callAssign targets signature.id arguments, { context with scope })

private def checkCondition (condition : Syntax.Expr) (message : String) : CheckM Checked.Expr := do
  let (value, ty) ← (checkTyped Ty.bool condition).run (← read)
  unless ty == .bool do throw (diagnosticAt condition.span message)
  return value

mutual
  private partial def checkStatement (statement : Syntax.Stmt) : CheckM (Checked.Stmt × Context) := do
    let context ← read
    match statement with
    | .expr (.call callee arguments span) =>
      if callee.text == "println" then
        return (← checkPrintln callee arguments span, context)
      let name := callee.text.copy
      if let .error error := checkCallable context.scope name callee.span then throw error
      let some signature := context.all[name]?
        | throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
      if signature.name == "main" then
        throw (diagnosticAt callee.span "cannot call 'main'")
      let checked ← (checkArguments signature arguments span).run context
      return (.call signature.id checked, context)
    | .multiAssignment names define value => checkMultiAssignment names define value
    | .varDeclaration name typeName initializer => checkDeclaration name typeName initializer
    | .assignment name value => do
      let some symbol := context.scope.find? name.text.copy
        | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
      let (value', ty) ← (checkTyped symbol.ty value).run context
      unless ty == symbol.ty do
        throw (diagnosticAt value.span "assignment type does not match variable type")
      return (.assign symbol.id value', context)
    | .expr value => throw (diagnosticAt value.span "only function calls may be used as statements")
    | .return values span => do
      let signature := context.signature
      let results := signature.results
      -- `return f()` forwards every result of a call to a function with the same results.
      if let #[.call callee arguments callSpan] := values then
        let forwarded? := if results.size ≥ 2 then context.all[callee.text.copy]? else none
        if let some forwarded := forwarded? then
          if let .error error := checkCallable context.scope callee.text.copy callee.span then throw error
          unless forwarded.results == results do
            throw (diagnosticAt callee.span
              s!"results of {callee.text}() do not match the results of function '{signature.name}'")
          let checked ← (checkArguments forwarded arguments callSpan).run context
          return (.returnCall forwarded.id checked, context)
      if let some first := values[0]? then
        if results.isEmpty then
          throw (diagnosticAt first.span s!"function '{signature.name}' returns no value")
      else if !results.isEmpty then
        throw (diagnosticAt span s!"function '{signature.name}' must return a value")
      if values.size < results.size then
        throw (diagnosticAt span s!"not enough return values in function '{signature.name}'")
      if let some extra := values[results.size]? then
        throw (diagnosticAt extra.span s!"too many return values in function '{signature.name}'")
      let mut checked := #[]
      for value in values, expected in results do
        let (value', ty) ← (checkTyped expected value).run context
        unless ty == expected do
          throw (diagnosticAt value.span s!"return value must be {expected.name}")
        checked := checked.push value'
      return (.return checked, context)
    | .break span => do
      if context.loopDepth == 0 then throw (diagnosticAt span "break outside loop")
      return (.break, context)
    | .continue span => do
      if context.loopDepth == 0 then throw (diagnosticAt span "continue outside loop")
      return (.continue, context)
    | .ifThen condition body elseBody => do
      let value ← checkCondition condition "if condition must be bool"
      let yes ← withScope context.scope.enter (checkStatements body)
      let no ← elseBody.mapM fun statements => withScope context.scope.enter (checkStatements statements)
      return (.ifThen value yes no, context)
    | .forLoop initializer condition post body => do
      let loopScope := context.scope.enter
      let (init, loopContext) ← match initializer with
        | some statement => do
          let (checked, next) ← withScope loopScope (checkStatement statement)
          pure (some checked, next)
        | none => pure (none, { context with scope := loopScope })
      let loopScope := loopContext.scope
      let test ← condition.mapM fun condition =>
        withScope loopScope (checkCondition condition "for condition must be bool")
      let bodyContext := { loopContext with scope := loopScope.enter, loopDepth := context.loopDepth + 1 }
      let body' ← withReader (fun _ => bodyContext) (checkStatements body)
      let post' ← post.mapM fun statement => do
        let (checked, _) ← withScope loopScope (checkStatement statement)
        return checked
      return (.forLoop init test post' body', context)

  private partial def checkStatements (statements : Array Syntax.Stmt) : CheckM (Array Checked.Stmt) := do
    let mut context ← read
    let mut checked := #[]
    for statement in statements do
      let (next, nextContext) ← withReader (fun _ => context) (checkStatement statement)
      checked := checked.push next
      context := nextContext
    return checked
end

private partial def hasOwnBreak (statements : Array Syntax.Stmt) : Bool :=
  statements.any fun statement =>
    match statement with
    | .break _ => true
    | .ifThen _ yes elseBody =>
      hasOwnBreak yes || (elseBody.map hasOwnBreak).getD false
    -- A nested loop consumes its own break.
    | .forLoop .. => false
    | .varDeclaration .. | .assignment .. | .multiAssignment .. | .expr _ | .return .. | .continue _ =>
      false

-- Return rules describe source syntax, even when CFG edges later make a path unreachable.
private partial def isTerminating (statements : Array Syntax.Stmt) : Bool :=
  match statements.back? with
  | some (.return ..) => true
  | some (.ifThen _ yes (some no)) => isTerminating yes && isTerminating no
  | some (.forLoop _ none _ body) => !hasOwnBreak body
  | _ => false

/-- Check the whole source, including unreachable statements, and resolve names to stable IDs. -/
def check (file : Syntax.File) : Except Diagnostic Checked.File := do
  if file.packageName.text != "main" then throw (diagnosticAt file.packageName.span "expected package main")
  -- Collect every signature before checking bodies to allow forward calls and recursion.
  let all ← signatures file
  let some main := all["main"]? | throw ⟨.check, none, "expected main function"⟩
  unless main.parameters.isEmpty && main.results.isEmpty do
    throw ⟨.check, (file.functions.find? (·.name.text == "main".toSlice)).map (·.span),
      "main must have no parameters or return value"⟩
  let mut functions := #[]
  for function in file.functions do
    let some signature := all[function.name.text.copy]?
      | throw (diagnosticAt function.name.span "internal error: missing function signature")
    let initial := signature.parameters.map (·.ty)
    let (body, locals) ← ((checkStatements function.body).run
      ⟨all, signature, signature.scope, 0⟩).run initial
    if !signature.results.isEmpty && !isTerminating function.body then
      throw (diagnosticAt function.span s!"function '{signature.name}' must end with return")
    functions := functions.push ⟨signature.name, signature.parameters, locals,
      signature.results, body⟩
  return ⟨functions⟩

end GoAot.Check
