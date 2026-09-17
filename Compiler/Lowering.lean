module

public import Compiler.Scope
public import Compiler.Parser.Go
import Compiler.Literal
import Std.Data.HashMap

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

private def signatures (file : Syntax.File) : Except Diagnostic (Std.HashMap String Signature) := do
  let mut result : Std.HashMap String Signature := {}
  for function in file.functions do
    let name := function.name.text.copy
    unless IR.validName name do throw (diagnosticAt function.name.span s!"unsupported function name '{name}'")
    if result.contains name then
      throw (diagnosticAt function.name.span s!"duplicate function '{name}'")
    let mut parameters := #[]
    let mut scope := Scope.empty
    for parameter in function.parameters do
      if parameter.typeName.text != "int" then
        throw (diagnosticAt parameter.typeName.span s!"only int parameters are supported in function '{name}'")
      let parameterName := parameter.name.text.copy
      unless IR.validName parameterName do
        throw (diagnosticAt parameter.name.span s!"unsupported parameter name '{parameter.name.text}'")
      scope ← scope.declare parameterName
        ⟨.parameter, parameters.size, .int, parameter.name.span⟩
      parameters := parameters.push parameterName
    let returnsInt ← match function.resultType with
      | none => pure false
      | some resultType =>
        if resultType.text == "int" then pure true
        else throw (diagnosticAt resultType.span s!"only int return values are supported in function '{name}'")
    result := result.insert name ⟨name, parameters, returnsInt, scope⟩
  return result

private def decodeString (literal : String) (span : Span) : Except Diagnostic ByteArray :=
  if literal.startsWith "\"" then return Literal.decodeInterpreted literal
  else throw (diagnosticAt span "raw string literals are not supported yet")

private structure PendingBlock where
  instructions : Array IR.Instruction := #[]
  terminator : Option IR.Terminator := none

private structure LoopContext where
  -- Targets are allocated when a live branch first needs them.
  breakTarget : Option IR.BlockId
  continueTarget : Option IR.BlockId

private structure Builder where
  blocks : Array PendingBlock := #[{}]
  current : Option IR.BlockId := some 0
  nextValue : IR.ValueId := 0
  /-- Slot kinds indexed by slot ID, emitted as entry block allocations by `Builder.finish`. -/
  slots : Array IR.ValueKind := #[]
  loops : List LoopContext := []

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

private def Builder.suspend (builder : Builder) : Option IR.BlockId × Builder :=
  (builder.current, { builder with current := none })

private def Builder.popLoop (builder : Builder) : Except Diagnostic (LoopContext × Builder) := do
  let context :: rest := builder.loops | throw builderError
  return (context, { builder with loops := rest })

private def Builder.jump (builder : Builder) (isBreak : Bool) : Except Diagnostic Builder := do
  let context :: rest := builder.loops | throw builderError
  if builder.current.isNone then return builder

  let existing := if isBreak then context.breakTarget else context.continueTarget
  let (target, builder) := match existing with
    | some target => (target, builder)
    | none =>
      let (target, builder) := builder.newBlock
      let context := if isBreak then { context with breakTarget := some target }
        else { context with continueTarget := some target }
      (target, { builder with loops := context :: rest })

  builder.terminate (.br target)

/--
Finalizes terminated blocks and prepends slot allocations to the entry block.
Keeping allocations there makes them dominate all uses and lets LLVM promote them.
Initialization stores remain at their source declaration sites.
-/
private def Builder.finish (builder : Builder) : Except Diagnostic (Array IR.Block) := do
  if builder.current.isSome || !builder.loops.isEmpty then throw builderError
  let blocks := builder.blocks.modify 0 fun block =>
    let allocations := builder.slots.mapIdx fun slot kind => IR.Instruction.alloca slot kind
    { block with instructions := allocations ++ block.instructions }
  blocks.mapM fun block => do
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
private def checkCallable (scope : Scope) (name : String) (span : Span) : Except Diagnostic Unit := do
  if (scope.find? name).isSome then
    throw (diagnosticAt span s!"cannot call non-function '{name}'")

private structure LoweredOperand where
  operand : IR.Operand
  kind : IR.ValueKind
  builder : Builder

private partial def lowerOperand (all : Std.HashMap String Signature) (scope : Scope)
    (builder : Builder) : Syntax.Expr → Except Diagnostic LoweredOperand
  | .intLiteral text span => do
    let value := Literal.decodeInt text
    if value > IR.maxSignedInt64 then
      throw (diagnosticAt span "integer literal exceeds signed 64-bit range")
    return ⟨.literal value, .int, builder⟩
  | .identifier name => do
    let some symbol := scope.find? name.text.copy
      | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
    let (value, builder) ← builder.emitValue (.load · symbol.slot symbol.valueKind)
    return ⟨value, symbol.valueKind, builder⟩
  | .call callee arguments span => do
    let name := callee.text.copy
    checkCallable scope name callee.span
    let some signature := all[name]?
      | throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
    unless signature.returnsInt do
      throw (diagnosticAt callee.span s!"function '{callee.text}' does not return a value")
    if arguments.size != signature.parameters.size then
      throw (diagnosticAt span s!"function '{callee.text}' expects {signature.parameters.size} arguments")
    let mut lowered := #[]
    let mut builder := builder
    for argument in arguments do
      let ⟨value, kind, next⟩ ← lowerOperand all scope builder argument
      unless kind == .int do throw (diagnosticAt argument.span "function arguments must be int")
      lowered := lowered.push value
      builder := next
    let (value, next) ← builder.emitValue (.call · signature.name lowered)
    return ⟨value, .int, next⟩
  | .binary op left right span => do
    let ⟨left, leftKind, builder⟩ ← lowerOperand all scope builder left
    let ⟨right, rightKind, builder⟩ ← lowerOperand all scope builder right
    unless leftKind == .int && rightKind == .int do
      throw (diagnosticAt span "binary operands must be int")
    let (op, kind) : IR.Op × IR.ValueKind := match op with
      | .add => (.add, .int)
      | .subtract => (.subtract, .int)
      | .less => (.less, .bool)
    let (value, builder) ← builder.emitValue (.binary · op left right)
    return ⟨value, kind, builder⟩
  | .stringLiteral _ span => throw (diagnosticAt span "expected int expression")

private def lowerDeclaration (all : Std.HashMap String Signature) (scope : Scope)
    (builder : Builder) (name : Syntax.Ident) (typeName : Option Syntax.Ident)
    (initializer : Option Syntax.Expr) : Except Diagnostic (Scope × Builder) := do
  if typeName.isNone && initializer.isNone then
    throw (diagnosticAt name.span "variable declaration requires a type or initializer")
  let nameText := name.text.copy
  unless IR.validName nameText && nameText != "_" do
    throw (diagnosticAt name.span s!"unsupported local name '{nameText}'")
  if let some typeName := typeName then
    unless typeName.text == "int" do
      throw (diagnosticAt typeName.span "only int variable types are supported")
  -- Resolve the initializer before introducing the binding.
  let ⟨operand, kind, next⟩ ← match initializer with
    | some value => lowerOperand all scope builder value
    | none => pure ⟨.literal 0, .int, builder⟩
  if typeName.isSome && kind != .int then
    throw (diagnosticAt ((initializer.map (·.span)).getD name.span) "initializer must be int")
  let slot := next.slots.size
  let scope ← scope.declare nameText ⟨.local, slot, kind, name.span⟩
  -- Reserve slots even on closed paths; stores depend on reachability.
  let builder := { next with slots := next.slots.push kind }
  return (scope, ← builder.emit (.store slot kind operand))

private def lowerCondition (all : Std.HashMap String Signature) (scope : Scope)
    (builder : Builder) (condition : Syntax.Expr) (message : String) :
    Except Diagnostic LoweredOperand := do
  let lowered ← lowerOperand all scope builder condition
  unless lowered.kind == .bool do throw (diagnosticAt condition.span message)
  return lowered

mutual
  private partial def lowerStatement (all : Std.HashMap String Signature) (signature : Signature)
      (scope : Scope) (builder : Builder) : Syntax.Stmt → Except Diagnostic Builder
    | .expr (.call callee arguments span) => do
      let name := callee.text.copy
      checkCallable scope name callee.span
      if name != "println" then
        throw (diagnosticAt callee.span "only println calls may be used as statements")
      let some argument := arguments[0]?
        | throw (diagnosticAt span "println expects one argument")
      if arguments.size != 1 then throw (diagnosticAt span "println expects one argument")
      let (instruction, builder) ← match argument with
        | .stringLiteral literal span =>
          pure (IR.Instruction.printString (← decodeString literal span), builder)
        | _ => do
          let ⟨value, kind, builder⟩ ← lowerOperand all scope builder argument
          unless kind == .int do throw (diagnosticAt argument.span "println supports only string and int")
          pure (.printInt value, builder)
      builder.emit instruction
    -- Declarations update scope in lowerStatements or a for initializer.
    | .varDeclaration .. => throw builderError
    | .assignment name value => do
      let some symbol := scope.find? name.text.copy
        | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
      let ⟨operand, kind, builder⟩ ← lowerOperand all scope builder value
      unless kind == symbol.valueKind do
        throw (diagnosticAt value.span "assignment type does not match variable type")
      builder.emit (.store symbol.slot kind operand)
    | .expr value => throw (diagnosticAt value.span "only function calls may be used as statements")
    | .return value => do
      unless signature.returnsInt do throw (diagnosticAt value.span s!"function '{signature.name}' returns no value")
      let ⟨operand, kind, builder⟩ ← lowerOperand all scope builder value
      unless kind == .int do throw (diagnosticAt value.span "return value must be int")
      builder.terminate (.ret (some operand))
    | .break span => do
      if builder.loops.isEmpty then throw (diagnosticAt span "break outside loop")
      builder.jump (isBreak := true)
    | .continue span => do
      if builder.loops.isEmpty then throw (diagnosticAt span "continue outside loop")
      builder.jump (isBreak := false)
    | .ifThen condition body elseBody => do
      let ⟨operand, _, builder⟩ ← lowerCondition all scope builder condition "if condition must be bool"
      -- Closed paths still check source semantics, without reserving unreachable blocks.
      if builder.current.isNone then
        let builder ← lowerStatements all signature scope.enter builder body
        match elseBody with
        | some statements => return ← lowerStatements all signature scope.enter builder statements
        | none => return builder
      let (thenBlock, builder) := builder.newBlock
      let (elseBlock, builder) := builder.newBlock
      let builder ← builder.terminate (.condBr operand thenBlock elseBlock)
      let builder ← builder.selectBlock thenBlock
      let builder ← lowerStatements all signature scope.enter builder body
      match elseBody with
      | none => do
        let builder ← builder.terminate (.br elseBlock)
        builder.selectBlock elseBlock
      | some statements => do
          let (thenOpen, builder) := builder.suspend
          let builder ← builder.selectBlock elseBlock
          let builder ← lowerStatements all signature scope.enter builder statements
          if thenOpen.isNone && builder.current.isNone then return builder
          let (continuation, builder) := builder.newBlock
          let builder ← builder.terminate (.br continuation)
          let builder ← match thenOpen with
            | some block => do
              let builder ← builder.selectBlock block
              builder.terminate (.br continuation)
            | none => pure builder
          builder.selectBlock continuation
    | .forLoop initializer condition post body => do
      let loopScope := scope.enter
      let (loopScope, builder) ← match initializer with
        | some (.varDeclaration name typeName value) =>
          lowerDeclaration all loopScope builder name typeName value
        | some statement => do
          let builder ← lowerStatement all signature loopScope builder statement
          pure (loopScope, builder)
        | none => pure (loopScope, builder)

      if builder.current.isNone then
        let builder ← match condition with
          | some condition => do
            let ⟨_, _, builder⟩ ← lowerCondition all loopScope builder condition "for condition must be bool"
            pure builder
          | none => pure builder
        let builder := { builder with loops := ⟨none, none⟩ :: builder.loops }
        let builder ← lowerStatements all signature loopScope.enter builder body
        let (_, builder) ← builder.popLoop
        match post with
        | some statement => return ← lowerStatement all signature loopScope builder statement
        | none => return builder

      let (header, builder) := builder.newBlock
      let (loopBody, builder) := builder.newBlock
      let builder ← builder.terminate (.br header)
      let builder ← builder.selectBlock header
      let (exit, builder) ← match condition with
        | some condition => do
          let ⟨operand, _, builder⟩ ← lowerCondition all loopScope builder condition "for condition must be bool"
          let (exit, builder) := builder.newBlock
          pure (some exit, ← builder.terminate (.condBr operand loopBody exit))
        | none => pure (none, ← builder.terminate (.br loopBody))

      let builder ← builder.selectBlock loopBody
      let continueTarget := if post.isSome then none else some header
      let builder := { builder with loops := ⟨exit, continueTarget⟩ :: builder.loops }
      let builder ← lowerStatements all signature loopScope.enter builder body
      let builder ← builder.jump (isBreak := false)
      let (context, builder) ← builder.popLoop

      let builder ← match post, context.continueTarget with
        | some statement, some postBlock => do
          let builder ← builder.selectBlock postBlock
          let builder ← lowerStatement all signature loopScope builder statement
          builder.terminate (.br header)
        | some statement, none => lowerStatement all signature loopScope builder statement
        | none, _ => pure builder

      match context.breakTarget with
      | some exit => builder.selectBlock exit
      | none => return builder

  /--
  Lowers a statement sequence, making each declaration visible to subsequent statements.
  Scope changes remain within this sequence, while stores can update enclosing bindings.
  -/
  private partial def lowerStatements (all : Std.HashMap String Signature) (signature : Signature)
      (scope : Scope) (builder : Builder) (statements : Array Syntax.Stmt) : Except Diagnostic Builder := do
    let mut state := (scope, builder)
    for statement in statements do
      match statement with
      | .varDeclaration name typeName initializer =>
        state ← lowerDeclaration all state.1 state.2 name typeName initializer
      | _ => state := (state.1, ← lowerStatement all signature state.1 state.2 statement)
    return state.2
end

private partial def hasOwnBreak (statements : Array Syntax.Stmt) : Bool :=
  statements.any fun statement =>
    match statement with
    | .break _ => true
    | .ifThen _ yes elseBody =>
      hasOwnBreak yes || (elseBody.map hasOwnBreak).getD false
    -- A break inside a nested loop targets that nested loop.
    | .forLoop .. => false
    | .varDeclaration .. | .assignment .. | .expr _ | .return _ | .continue _ => false

private partial def isTerminating (statements : Array Syntax.Stmt) : Bool :=
  match statements.back? with
  | some (.return _) => true
  | some (.ifThen _ yes (some no)) => isTerminating yes && isTerminating no
  | some (.forLoop _ none _ body) => !hasOwnBreak body
  | _ => false

def lower (file : Syntax.File) : Except Diagnostic IR.Program := do
  if file.packageName.text != "main" then throw (diagnosticAt file.packageName.span "expected package main")
  let all ← signatures file
  let some main := all["main"]? | throw ⟨.lowering, none, "expected main function"⟩
  unless main.parameters.isEmpty && !main.returnsInt do
    throw ⟨.lowering, (file.functions.find? (·.name.text == "main".toSlice)).map (·.span),
      "main must have no parameters or return value"⟩
  let mut functions := #[]
  for function in file.functions do
    let some signature := all[function.name.text.copy]?
      | throw (diagnosticAt function.name.span "internal error: missing function signature")
    if signature.name != "main" && !signature.returnsInt then
      throw (diagnosticAt function.name.span s!"function '{signature.name}' must return int")
    -- Parameter slot IDs match argument indices, as reserved by signatures.
    -- Copy arguments once so parameter assignments share the local variable path.
    let mut initial : Builder := { slots := Array.replicate signature.parameters.size .int }
    for index in [:signature.parameters.size] do
      initial ← initial.emit (.store index .int (.argument index))
    let builder ← lowerStatements all signature signature.scope initial function.body
    if signature.returnsInt then
      unless isTerminating function.body do
        throw (diagnosticAt function.span s!"function '{signature.name}' must end with return")
    -- A valid int function either returns or loops forever on every path.
    let builder ← if signature.returnsInt then pure builder else builder.terminate (.ret none)
    let blocks ← builder.finish
    functions := functions.push ⟨signature.name, signature.parameters,
      if signature.returnsInt then .int else .void, blocks⟩
  return ⟨functions⟩

end GoAot.Lowering
