module

public import Compiler.Scope
public import Compiler.Parser.Go
import Compiler.Literal

public section

namespace GoAot.Lowering

private def diagnosticAt (span : Span) (message : String) : Diagnostic :=
  ⟨.lowering, some span, message⟩

private structure Signature where
  name : String
  parameters : Array String
  returnsInt : Bool
  -- Retain the body scope here to preserve duplicate parameter diagnostic order
  -- without rebuilding it before body lowering.
  scope : Scope

private def signatures (file : Syntax.File) : Except Diagnostic (Array Signature) := do
  let mut result := #[]
  for function in file.functions do
    let name := function.name.text
    unless IR.validName name do throw (diagnosticAt function.name.span s!"unsupported function name '{name}'")
    if result.any (fun (signature : Signature) => signature.name == name) then
      throw (diagnosticAt function.name.span s!"duplicate function '{name}'")
    let mut parameters := #[]
    let mut scope := Scope.empty
    for parameter in function.parameters do
      if parameter.typeName.text != "int" then
        throw (diagnosticAt parameter.typeName.span s!"only int parameters are supported in function '{name}'")
      unless IR.validName parameter.name.text do
        throw (diagnosticAt parameter.name.span s!"unsupported parameter name '{parameter.name.text}'")
      scope ← scope.declare parameter.name.text
        ⟨.parameter, .argument parameters.size, .int, parameter.name.span⟩
      parameters := parameters.push parameter.name.text
    let returnsInt ← match function.resultType with
      | none => pure false
      | some resultType =>
        if resultType.text == "int" then pure true
        else throw (diagnosticAt resultType.span s!"only int return values are supported in function '{name}'")
    result := result.push ⟨name, parameters, returnsInt, scope⟩
  return result

private def findSignature? (all : Array Signature) (name : String) : Option Signature :=
  all.find? fun signature => signature.name == name

private def decodeString (literal : String) (span : Span) : Except Diagnostic ByteArray := do
  match literal.toList with
  | '"' :: rest =>
    match rest.reverse with
    | '"' :: reversed => (Literal.decodeInterpreted reversed.reverse).mapError (diagnosticAt span)
    | _ => throw (diagnosticAt span "unterminated string literal")
  | _ => throw (diagnosticAt span "raw string literals are not supported yet")

private structure PendingBlock where
  instructions : Array IR.Instruction := #[]
  terminator : Option IR.Terminator := none

private structure Builder where
  blocks : Array PendingBlock := #[{}]
  current : Option IR.BlockId := some 0
  nextValue : IR.ValueId := 0

private def builderError : Diagnostic :=
  ⟨.lowering, none, "internal error: invalid CFG builder state"⟩

private def Builder.newBlock (builder : Builder) : IR.BlockId × Builder :=
  (builder.blocks.size, { builder with blocks := builder.blocks.push {} })

-- A closed path has no current block, so emitting there is a no-op rather than an error.
-- Keeping that rule here means statement lowering never repeats the reachability test.
private def Builder.emit (builder : Builder) (instruction : IR.Instruction) :
    Except Diagnostic Builder := do
  let some current := builder.current | return builder
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  -- `block` above shares the instruction array with `blocks`. Pushing through it copied the whole
  -- array on every emit. `modify` takes the element out first, allowing the push to happen in place.
  let blocks := builder.blocks.modify current fun block =>
    { block with instructions := block.instructions.push instruction }
  return { builder with blocks }

private def Builder.terminate (builder : Builder) (terminator : IR.Terminator) :
    Except Diagnostic Builder := do
  let some current := builder.current | return builder
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  return { builder with
    blocks := builder.blocks.set! current { block with terminator := some terminator }
    current := none }

private def Builder.selectBlock (builder : Builder) (target : IR.BlockId) :
    Except Diagnostic Builder := do
  let some block := builder.blocks[target]? | throw builderError
  if builder.current.isSome || block.terminator.isSome then throw builderError
  return { builder with current := some target }

private def Builder.finish (builder : Builder) : Except Diagnostic (Array IR.Block) := do
  if builder.current.isSome then throw builderError
  builder.blocks.mapM fun block => do
    let some terminator := block.terminator | throw builderError
    return ⟨block.instructions, terminator⟩

private def Builder.emitValue (builder : Builder) (instruction : IR.ValueId → IR.Instruction) :
    Except Diagnostic (IR.Operand × Builder) := do
  -- Unlike emit, this cannot delegate: a closed path must not consume a value id, and
  -- returning `.value` would name a definition that never exists. Dead source still checks
  -- kinds, but the placeholder is discarded by emit and never enters the live CFG.
  if builder.current.isNone then return (.literal 0, builder)
  let id := builder.nextValue
  let builder ← builder.emit (instruction id)
  return (.value id, { builder with nextValue := id + 1 })

-- A local shadows every function of the same name, including println, as in Go.
private def checkCallable (scope : Scope) (callee : Syntax.Ident) : Except Diagnostic Unit := do
  if (scope.find? callee.text).isSome then
    throw (diagnosticAt callee.span s!"cannot call non-function '{callee.text}'")

private partial def lowerOperand (all : Array Signature) (scope : Scope)
    (builder : Builder) : Syntax.Expr → Except Diagnostic (IR.Operand × IR.ValueKind × Builder)
  | .intLiteral text span =>
    match text.toNat? with
    | some value => do
      if value > 9223372036854775807 then
        throw (diagnosticAt span "integer literal exceeds signed 64-bit range")
      return (.literal value, .int, builder)
    | none => throw (diagnosticAt span s!"unsupported integer literal '{text}'")
  | .identifier name => do
    let some symbol := scope.find? name.text
      | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
    return (symbol.operand, symbol.valueKind, builder)
  | .call callee arguments span => do
    checkCallable scope callee
    let some signature := findSignature? all callee.text
      | throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
    unless signature.returnsInt do
      throw (diagnosticAt callee.span s!"function '{callee.text}' does not return a value")
    if arguments.size != signature.parameters.size then
      throw (diagnosticAt span s!"function '{callee.text}' expects {signature.parameters.size} arguments")
    let mut lowered := #[]
    let mut builder := builder
    for argument in arguments do
      let (value, kind, next) ← lowerOperand all scope builder argument
      unless kind == .int do throw (diagnosticAt argument.span "function arguments must be int")
      lowered := lowered.push value
      builder := next
    let (value, next) ← builder.emitValue (.call · callee.text lowered)
    return (value, .int, next)
  | .binary op left right span => do
    let (left, leftKind, builder) ← lowerOperand all scope builder left
    let (right, rightKind, builder) ← lowerOperand all scope builder right
    unless leftKind == .int && rightKind == .int do
      throw (diagnosticAt span "binary operands must be int")
    let (op, kind) : IR.Op × IR.ValueKind := match op with
      | .add => (.add, .int)
      | .subtract => (.subtract, .int)
      | .less => (.less, .bool)
    let (value, builder) ← builder.emitValue (.binary · op left right)
    return (value, kind, builder)
  | .stringLiteral _ span => throw (diagnosticAt span "expected int expression")

mutual
  private partial def lowerStatement (all : Array Signature) (signature : Signature) (scope : Scope)
      (builder : Builder) : Syntax.Stmt → Except Diagnostic Builder
    | .expr (.call callee arguments span) => do
      checkCallable scope callee
      if callee.text != "println" then
        throw (diagnosticAt callee.span "only println calls may be used as statements")
      let some argument := arguments[0]?
        | throw (diagnosticAt span "println expects one argument")
      if arguments.size != 1 then throw (diagnosticAt span "println expects one argument")
      let (instruction, builder) ← match argument with
        | .stringLiteral literal span =>
          pure (IR.Instruction.printString (← decodeString literal span), builder)
        | _ => do
          let (value, kind, builder) ← lowerOperand all scope builder argument
          unless kind == .int do throw (diagnosticAt argument.span "println supports only string and int")
          pure (.printInt value, builder)
      builder.emit instruction
    | .expr value => throw (diagnosticAt value.span "only function calls may be used as statements")
    | .return value => do
      unless signature.returnsInt do throw (diagnosticAt value.span s!"function '{signature.name}' returns no value")
      let (operand, kind, builder) ← lowerOperand all scope builder value
      unless kind == .int do throw (diagnosticAt value.span "return value must be int")
      builder.terminate (.ret (some operand))
    | .ifThen condition body => do
      let (operand, kind, builder) ← lowerOperand all scope builder condition
      unless kind == .bool do throw (diagnosticAt condition.span "if condition must be bool")
      -- Closed paths still check source semantics, without reserving unreachable blocks.
      if builder.current.isNone then return ← lowerStatements all signature scope.enter builder body
      let (thenBlock, builder) := builder.newBlock
      let (continuation, builder) := builder.newBlock
      let builder ← builder.terminate (.condBr operand thenBlock continuation)
      let builder ← builder.selectBlock thenBlock
      let builder ← lowerStatements all signature scope.enter builder body
      let builder ← builder.terminate (.br continuation)
      builder.selectBlock continuation

  private partial def lowerStatements (all : Array Signature) (signature : Signature) (scope : Scope)
      (builder : Builder) (statements : Array Syntax.Stmt) : Except Diagnostic Builder := do
    let mut builder := builder
    for statement in statements do
      builder ← lowerStatement all signature scope builder statement
    return builder
end

def lower (file : Syntax.File) : Except Diagnostic IR.Program := do
  if file.packageName.text != "main" then throw (diagnosticAt file.packageName.span "expected package main")
  let all ← signatures file
  let some main := findSignature? all "main" | throw ⟨.lowering, none, "expected main function"⟩
  unless main.parameters.isEmpty && !main.returnsInt do
    throw ⟨.lowering, (file.functions.find? (·.name.text == "main")).map (·.span),
      "main must have no parameters or return value"⟩
  let mut functions := #[]
  for function in file.functions do
    let some signature := findSignature? all function.name.text
      | throw (diagnosticAt function.name.span "internal error: missing function signature")
    if signature.name != "main" && !signature.returnsInt then
      throw (diagnosticAt function.name.span s!"function '{signature.name}' must return int")
    let builder ← lowerStatements all signature signature.scope {} function.body
    if signature.returnsInt then
      match function.body.back? with
      | some (.return _) => pure ()
      | _ => throw (diagnosticAt function.span s!"function '{signature.name}' must end with return")
    -- An int function's body ends with return, so its last block is already closed;
    -- leaving one open here fails Builder.finish.
    let builder ← if signature.returnsInt then pure builder else builder.terminate (.ret none)
    let blocks ← builder.finish
    functions := functions.push ⟨signature.name, signature.parameters,
      if signature.returnsInt then .int else .void, blocks⟩
  return ⟨functions⟩

end GoAot.Lowering
