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

private partial def lowerExpr : Checked.Expr → LowerM IR.Operand
  | .intLiteral value => return .literal value
  | .local id => do
    let some kind := (← read).function.locals[id]? | throw lowerError
    emitValue (.load · id kind)
  | .call id arguments => do
    let some function := (← read).file.functions[id]? | throw lowerError
    let mut lowered := #[]
    for argument in arguments do
      lowered := lowered.push (← lowerExpr argument)
    emitValue (.call · function.name lowered)
  | .binary op left right => do
    let left ← lowerExpr left
    let right ← lowerExpr right
    emitValue (.binary · op left right)

mutual
  private partial def lowerStatement (statement : Checked.Stmt) : LowerM Unit := do
    -- A statement after a terminator starts an unconnected block that `finish` can discard.
    startStatement
    match statement with
    | .declare id initializer | .assign id initializer =>
      let some kind := (← read).function.locals[id]? | throw lowerError
      emit (.store id kind (← lowerExpr initializer))
    | .printString bytes => emit (.printString bytes)
    | .printInt value => emit (.printInt (← lowerExpr value))
    | .callVoid id arguments =>
      let some function := (← read).file.functions[id]? | throw lowerError
      let mut lowered := #[]
      for argument in arguments do
        lowered := lowered.push (← lowerExpr argument)
      emit (.callVoid function.name lowered)
    | .discard value => discard (lowerExpr value)
    | .return value => terminate (.ret (← value.mapM lowerExpr))
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
    for index in [:function.parameters.size] do
      initial ← initial.emit (.store index .int (.argument index))
    let (_, builder) ← ((lowerStatements function.body).run ⟨file, function⟩).run initial
    let builder ← match function.returnKind with
      | .int => pure builder
      | .void => builder.terminate (.ret none)
    let blocks ← builder.finish
    functions := functions.push ⟨function.name, function.parameters, function.returnKind, blocks⟩
  return ⟨functions⟩

end GoAot.Lowering
