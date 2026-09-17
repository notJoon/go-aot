module

public import Compiler.Scope
public import Compiler.Parser.Go
import Compiler.Literal
import Compiler.Lowering.Builder
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

private structure Context where
  all : Std.HashMap String Signature
  signature : Signature
  scope : Scope

private abbrev LowerM := ReaderT Context (StateT Builder (Except Diagnostic))

-- Pass the builder directly to its operation so `get` cannot retain an alias to its arrays.
@[inline] private def runBuilder (operation : Builder → Except Diagnostic (α × Builder)) : LowerM α :=
  fun _ builder => operation builder

@[inline] private def updateBuilder (operation : Builder → Except Diagnostic Builder) : LowerM Unit :=
  runBuilder fun builder => (operation builder).map ((), ·)

@[inline] private def updateContext (operation : Builder → Except Diagnostic Builder) : LowerM Context :=
  fun context builder => (operation builder).map (context, ·)

@[inline] private def emit (instruction : IR.Instruction) : LowerM Unit :=
  updateBuilder (·.emit instruction)

@[inline] private def emitValue (instruction : IR.ValueId → IR.Instruction) : LowerM IR.Operand :=
  runBuilder (·.emitValue instruction)

@[inline] private def terminate (terminator : IR.Terminator) : LowerM Unit :=
  updateBuilder (·.terminate terminator)

@[inline] private def selectBlock (target : IR.BlockId) : LowerM Unit :=
  updateBuilder (·.selectBlock target)

@[inline] private def jump (isBreak : Bool) : LowerM Unit :=
  updateBuilder (·.jump isBreak)

@[inline] private def newBlock : LowerM IR.BlockId :=
  fun _ builder => pure builder.newBlock

@[inline] private def suspend : LowerM (Option IR.BlockId) :=
  fun _ builder => pure builder.suspend

@[inline] private def popLoop : LowerM LoopContext :=
  runBuilder (·.popLoop)

@[inline] private def withScope (scope : Scope) (action : LowerM α) : LowerM α :=
  withReader (fun context => { context with scope }) action

private structure LoweredOperand where
  operand : IR.Operand
  kind : IR.ValueKind

private partial def lowerOperand : Syntax.Expr → LowerM LoweredOperand
  | .intLiteral text span => do
    let value := Literal.decodeInt text
    if value > IR.maxSignedInt64 then
      throw (diagnosticAt span "integer literal exceeds signed 64-bit range")
    return ⟨.literal value, .int⟩
  | .identifier name => do
    let some symbol := (← read).scope.find? name.text.copy
      | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
    let value ← emitValue (.load · symbol.slot symbol.valueKind)
    return ⟨value, symbol.valueKind⟩
  | .call callee arguments span => do
    let name := callee.text.copy
    -- A local shadows every function of the same name, including println, as in Go.
    if ((← read).scope.find? name).isSome then
      throw (diagnosticAt callee.span s!"cannot call non-function '{name}'")
    let some signature := (← read).all[name]?
      | throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
    unless signature.returnsInt do
      throw (diagnosticAt callee.span s!"function '{callee.text}' does not return a value")
    if arguments.size != signature.parameters.size then
      throw (diagnosticAt span s!"function '{callee.text}' expects {signature.parameters.size} arguments")
    let mut lowered := #[]
    for argument in arguments do
      let ⟨value, kind⟩ ← lowerOperand argument
      unless kind == .int do throw (diagnosticAt argument.span "function arguments must be int")
      lowered := lowered.push value
    let value ← emitValue (.call · signature.name lowered)
    return ⟨value, .int⟩
  | .binary op left right span => do
    let ⟨left, leftKind⟩ ← lowerOperand left
    let ⟨right, rightKind⟩ ← lowerOperand right
    unless leftKind == .int && rightKind == .int do
      throw (diagnosticAt span "binary operands must be int")
    let (op, kind) : IR.Op × IR.ValueKind := match op with
      | .add => (.add, .int)
      | .subtract => (.subtract, .int)
      | .less => (.less, .bool)
    let value ← emitValue (.binary · op left right)
    return ⟨value, kind⟩
  | .stringLiteral _ span => throw (diagnosticAt span "expected int expression")

private def lowerDeclaration (name : Syntax.Ident) (typeName : Option Syntax.Ident)
    (initializer : Option Syntax.Expr) : LowerM Context := do
  if typeName.isNone && initializer.isNone then
    throw (diagnosticAt name.span "variable declaration requires a type or initializer")
  let nameText := name.text.copy
  unless IR.validName nameText && nameText != "_" do
    throw (diagnosticAt name.span s!"unsupported local name '{nameText}'")
  if let some typeName := typeName then
    unless typeName.text == "int" do
      throw (diagnosticAt typeName.span "only int variable types are supported")
  -- Resolve the initializer before introducing the binding.
  let ⟨operand, kind⟩ ← match initializer with
    | some value => lowerOperand value
    | none => pure ⟨.literal 0, .int⟩
  if typeName.isSome && kind != .int then
    throw (diagnosticAt ((initializer.map (·.span)).getD name.span) "initializer must be int")
  let slot ← modifyGet fun builder => (builder.slots.size, builder)
  let context ← read
  let scope ← context.scope.declare nameText ⟨.local, slot, kind, name.span⟩
  -- Reserve slots even on closed paths; stores depend on reachability.
  modify fun builder => { builder with slots := builder.slots.push kind }
  emit (.store slot kind operand)
  return { context with scope }

private def lowerCondition (condition : Syntax.Expr) (message : String) : LowerM IR.Operand := do
  let lowered ← lowerOperand condition
  unless lowered.kind == .bool do throw (diagnosticAt condition.span message)
  return lowered.operand

mutual
  private partial def lowerStatement : Syntax.Stmt → LowerM Context
    | .expr (.call callee arguments span) => do
      let name := callee.text.copy
      if ((← read).scope.find? name).isSome then
        throw (diagnosticAt callee.span s!"cannot call non-function '{name}'")
      if name != "println" then
        throw (diagnosticAt callee.span "only println calls may be used as statements")
      let some argument := arguments[0]?
        | throw (diagnosticAt span "println expects one argument")
      if arguments.size != 1 then throw (diagnosticAt span "println expects one argument")
      match argument with
        | .stringLiteral literal span =>
          updateContext (·.emit (.printString (← decodeString literal span)))
        | _ => do
          let ⟨value, kind⟩ ← lowerOperand argument
          unless kind == .int do throw (diagnosticAt argument.span "println supports only string and int")
          updateContext (·.emit (.printInt value))
    | .varDeclaration name typeName initializer =>
      lowerDeclaration name typeName initializer
    | .assignment name value => do
      let some symbol := (← read).scope.find? name.text.copy
        | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
      let ⟨operand, kind⟩ ← lowerOperand value
      unless kind == symbol.valueKind do
        throw (diagnosticAt value.span "assignment type does not match variable type")
      updateContext (·.emit (.store symbol.slot kind operand))
    | .expr value => throw (diagnosticAt value.span "only function calls may be used as statements")
    | .return value => do
      let signature := (← read).signature
      unless signature.returnsInt do throw (diagnosticAt value.span s!"function '{signature.name}' returns no value")
      let ⟨operand, kind⟩ ← lowerOperand value
      unless kind == .int do throw (diagnosticAt value.span "return value must be int")
      updateContext (·.terminate (.ret (some operand)))
    | .break span => do
      if (← get).loops.isEmpty then throw (diagnosticAt span "break outside loop")
      updateContext (·.jump (isBreak := true))
    | .continue span => do
      if (← get).loops.isEmpty then throw (diagnosticAt span "continue outside loop")
      updateContext (·.jump (isBreak := false))
    | .ifThen condition body elseBody => do
      let context ← read
      let scope := context.scope
      let operand ← lowerCondition condition "if condition must be bool"
      -- Closed paths still check source semantics, without reserving unreachable blocks.
      if (← get).current.isNone then
        withScope scope.enter (lowerStatements body)
        if let some statements := elseBody then
          withScope scope.enter (lowerStatements statements)
        return context
      let thenBlock ← newBlock
      let elseBlock ← newBlock
      terminate (.condBr operand thenBlock elseBlock)
      selectBlock thenBlock
      withScope scope.enter (lowerStatements body)
      match elseBody with
      | none =>
        terminate (.br elseBlock)
        selectBlock elseBlock
      | some statements =>
        let thenOpen ← suspend
        selectBlock elseBlock
        withScope scope.enter (lowerStatements statements)
        if thenOpen.isNone && (← get).current.isNone then return context
        let continuation ← newBlock
        terminate (.br continuation)
        if let some block := thenOpen then
          selectBlock block
          terminate (.br continuation)
        selectBlock continuation
      return context
    | .forLoop initializer condition post body => do
      let context ← read
      let scope := context.scope
      let loopScope := scope.enter
      let loopContext ← match initializer with
        | some statement => withScope loopScope (lowerStatement statement)
        | none => pure { context with scope := loopScope }
      let loopScope := loopContext.scope

      if (← get).current.isNone then
        if let some condition := condition then
          let _ ← withScope loopScope (lowerCondition condition "for condition must be bool")
        modify fun builder => { builder with loops := ⟨none, none⟩ :: builder.loops }
        withScope loopScope.enter (lowerStatements body)
        let _ ← popLoop
        if let some statement := post then
          let _ ← withScope loopScope (lowerStatement statement)
        return context

      let header ← newBlock
      let loopBody ← newBlock
      terminate (.br header)
      selectBlock header
      let exit ← match condition with
        | some condition => do
          let operand ← withScope loopScope (lowerCondition condition "for condition must be bool")
          let exit ← newBlock
          terminate (.condBr operand loopBody exit)
          pure (some exit)
        | none =>
          terminate (.br loopBody)
          pure none

      selectBlock loopBody
      let continueTarget := if post.isSome then none else some header
      modify fun builder => { builder with loops := ⟨exit, continueTarget⟩ :: builder.loops }
      withScope loopScope.enter (lowerStatements body)
      jump (isBreak := false)
      let loopControl ← popLoop

      if let some statement := post then
        if let some postBlock := loopControl.continueTarget then
          selectBlock postBlock
          let _ ← withScope loopScope (lowerStatement statement)
          terminate (.br header)
        else
          let _ ← withScope loopScope (lowerStatement statement)

      if let some exit := loopControl.breakTarget then selectBlock exit
      return context

  /--
  Lowers a statement sequence, making each declaration visible to subsequent statements.
  Scope changes remain within this sequence, while stores can update enclosing bindings.
  -/
  private partial def lowerStatements (statements : Array Syntax.Stmt) : LowerM Unit := do
    let mut context ← read
    for statement in statements do
      -- Only declarations replace the context; other statements reuse it.
      context ← withReader (fun _ => context) (lowerStatement statement)
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
    let (_, builder) ← ((lowerStatements function.body).run ⟨all, signature, signature.scope⟩).run initial
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
