module

public import Compiler.Checked
public import Compiler.Diagnostic
import Compiler.Lowering.Builder

public section

namespace GoAot.Lowering

private def lowerError : Diagnostic :=
  ⟨.lowering, none, "internal error: invalid checked syntax"⟩

private structure Context where
  file : Checked.File
  function : Checked.Function

private abbrev LowerM := ReaderT Context (StateT Builder (Except Diagnostic))

-- Pass the builder directly so reading state does not retain aliases to its arrays.
@[inline] private def runBuilder (operation : Builder → Except Diagnostic (α × Builder)) : LowerM α :=
  fun _ builder => operation builder

@[inline] private def updateBuilder (operation : Builder → Except Diagnostic Builder) : LowerM Unit :=
  runBuilder fun builder => (operation builder).map ((), ·)

@[inline] private def emit (instruction : IR.Instruction) : LowerM Unit :=
  updateBuilder (·.emit instruction)

@[inline] private def emitValue (instruction : IR.ValueId → IR.Instruction) : LowerM IR.Operand :=
  runBuilder (·.emitValue instruction)

@[inline] private def terminate (terminator : IR.Terminator) : LowerM Unit :=
  updateBuilder (·.terminate terminator)

@[inline] private def branchIfOpen (target : IR.BlockId) : LowerM Unit :=
  updateBuilder (·.branchIfOpen target)

@[inline] private def startStatement : LowerM Unit :=
  updateBuilder (·.startStatement)

@[inline] private def selectBlock (target : IR.BlockId) : LowerM Unit :=
  updateBuilder (·.selectBlock target)

@[inline] private def jump (isBreak : Bool) : LowerM Unit :=
  updateBuilder (·.jump isBreak)

@[inline] private def newBlock : LowerM IR.BlockId :=
  fun _ builder => pure builder.newBlock

/-- Whether lowering `expr` ends in a different block than it starts in. -/
private partial def branches : Checked.Expr → Bool
  | .and .. | .or .. => true
  | .call _ arguments => arguments.any branches
  | .binary _ _ left right | .shift _ _ left _ right => branches left || branches right
  | .convert _ _ value => branches value
  | .intLiteral _ | .floatLiteral _ | .boolLiteral _ | .local _ => false

private def typeOf : Checked.Expr → LowerM Ty
  | .local id => do
    let some ty := (← read).function.locals[id]? | throw lowerError
    return ty
  | .call id _ => do
    let some { results := #[ty], .. } := (← read).file.functions[id]? | throw lowerError
    return ty
  | .binary op ty _ _ => return if op.isComparison then .bool else ty
  | .shift _ ty .. | .convert _ ty _ => return ty
  | .intLiteral _ => return .int
  | .floatLiteral _ => return .float64
  | .boolLiteral _ | .and .. | .or .. => return .bool

private partial def lowerExpr : Checked.Expr → LowerM IR.Operand
  | .intLiteral value => return .literal value
  | .floatLiteral value => return .floatLiteral value
  | .boolLiteral value => return .boolLiteral value
  | .local id => do
    let some ty := (← read).function.locals[id]? | throw lowerError
    emitValue (.load · id ty)
  | .call id arguments => do
    let some function := (← read).file.functions[id]? | throw lowerError
    let lowered ← lowerOperands arguments
    emitValue (.call #[·] function.name lowered)
  | .binary op ty left right => do
    let #[left, right] ← lowerOperands #[left, right] | throw lowerError
    emitValue (.binary · op ty left right)
  | .shift op ty value countTy count => do
    let #[value, count] ← lowerOperands #[value, count] | throw lowerError
    emitValue (.shift · op ty value countTy count)
  | .convert source target value => do
    let value ← lowerExpr value
    emitValue (.convert · source target value)
  | .and left right => shortCircuit true left right
  | .or left right => shortCircuit false left right
where
  -- Values cannot cross blocks, so an operand followed by a short circuit waits in a slot.
  lowerOperands (operands : Array Checked.Expr) : LowerM (Array IR.Operand) := do
    let mut lowered : Array (IR.Operand ⊕ (IR.SlotId × Ty)) := #[]
    for h : index in [:operands.size] do
      let operand ← lowerExpr operands[index]
      if operand matches .value _ && (operands.extract (index + 1)).any branches then
        let ty ← typeOf operands[index]
        let slot ← fun _ builder => pure (builder.newSlot ty)
        emit (.store slot ty operand)
        lowered := lowered.push (.inr (slot, ty))
      else lowered := lowered.push (.inl operand)
    lowered.mapM fun
      | .inl operand => pure operand
      | .inr (slot, ty) => emitValue (.load · slot ty)
  -- Values cannot cross blocks, so both paths store the result in a temporary slot.
  shortCircuit (isAnd : Bool) (left right : Checked.Expr) : LowerM IR.Operand := do
    let slot ← fun _ builder => pure (builder.newSlot .bool)
    let leftValue ← lowerExpr left
    emit (.store slot .bool leftValue)
    let rightBlock ← newBlock
    let done ← newBlock
    terminate (if isAnd then .condBr leftValue rightBlock done else .condBr leftValue done rightBlock)
    selectBlock rightBlock
    emit (.store slot .bool (← lowerExpr right))
    terminate (.br done)
    selectBlock done
    emitValue (.load · slot .bool)

mutual
  private partial def lowerStatement (statement : Checked.Stmt) : LowerM Unit := do
    -- A statement after a terminator starts an unconnected block that `finish` can discard.
    startStatement
    match statement with
    | .declare id initializer | .assign id initializer =>
      let some ty := (← read).function.locals[id]? | throw lowerError
      emit (.store id ty (← lowerExpr initializer))
    | .printString bytes => emit (.printString bytes)
    | .print ty value => emit (.print ty (← lowerExpr value))
    | .call id arguments =>
      let some function := (← read).file.functions[id]? | throw lowerError
      let arguments ← lowerExpr.lowerOperands arguments
      let results ← fun _ builder => pure (builder.freshValues function.results.size)
      emit (.call results function.name arguments)
    | .callAssign targets id arguments =>
      let some function := (← read).file.functions[id]? | throw lowerError
      let arguments ← lowerExpr.lowerOperands arguments
      let results ← fun _ builder => pure (builder.freshValues function.results.size)
      emit (.call results function.name arguments)
      for target in targets, result in results, ty in function.results do
        if let some slot := target then emit (.store slot ty (.value result))
    | .return values => terminate (.ret (← lowerExpr.lowerOperands values))
    | .returnCall id arguments =>
      let some function := (← read).file.functions[id]? | throw lowerError
      let arguments ← lowerExpr.lowerOperands arguments
      let results ← fun _ builder => pure (builder.freshValues function.results.size)
      emit (.call results function.name arguments)
      terminate (.ret (results.map .value))
    | .break => jump (isBreak := true)
    | .continue => jump (isBreak := false)
    | .ifThen condition body elseBody =>
      let operand ← lowerExpr condition
      let thenBlock ← newBlock
      let elseBlock ← newBlock
      terminate (.condBr operand thenBlock elseBlock)
      selectBlock thenBlock
      lowerStatements body
      match elseBody with
      | none =>
        branchIfOpen elseBlock
        selectBlock elseBlock
      | some statements =>
        -- The continuation may have no incoming live edge when both arms return.
        let continuation ← newBlock
        branchIfOpen continuation
        selectBlock elseBlock
        lowerStatements statements
        branchIfOpen continuation
        selectBlock continuation
    | .forLoop initializer condition post body =>
      if let some statement := initializer then lowerStatement statement
      let header ← newBlock
      let loopBody ← newBlock
      let exit ← newBlock
      -- `continue` must have a fixed destination even before the body is lowered.
      let postBlock ← if post.isSome then some <$> newBlock else pure none
      branchIfOpen header
      selectBlock header
      match condition with
      | some condition => terminate (.condBr (← lowerExpr condition) loopBody exit)
      | none => terminate (.br loopBody)
      selectBlock loopBody
      modify fun builder => { builder with loops := ⟨exit, postBlock.getD header⟩ :: builder.loops }
      lowerStatements body
      branchIfOpen (postBlock.getD header)
      let _ ← runBuilder (·.popLoop)
      if let some statement := post then
        selectBlock postBlock.get!
        lowerStatement statement
        branchIfOpen header
      selectBlock exit

  private partial def lowerStatements (statements : Array Checked.Stmt) : LowerM Unit := do
    for statement in statements do lowerStatement statement
end

/-- Build CFGs from checked syntax. Invalid IDs are internal errors. -/
def lower (file : Checked.File) : Except Diagnostic IR.Program := do
  let mut functions := #[]
  for function in file.functions do
    -- All slots are allocated at entry. Declaration stores stay at their source sites.
    let mut initial : Builder := { slots := function.locals }
    for h : index in [:function.parameters.size] do
      initial ← initial.emit (.store index function.parameters[index].ty (.argument index))
    let (_, builder) ← ((lowerStatements function.body).run ⟨file, function⟩).run initial
    let builder ← if function.results.isEmpty then builder.terminate (.ret #[]) else pure builder
    let blocks ← builder.finish
    functions := functions.push ⟨function.name, function.parameters, function.results, blocks⟩
  return ⟨functions⟩

end GoAot.Lowering
