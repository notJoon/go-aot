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
  private partial def lowerStatement : Checked.Stmt → LowerM Unit
    | .declare id initializer | .assign id initializer => do
      let some kind := (← read).function.locals[id]? | throw lowerError
      emit (.store id kind (← lowerExpr initializer))
    | .printString bytes => emit (.printString bytes)
    | .printInt value => do emit (.printInt (← lowerExpr value))
    | .return value => do terminate (.ret (some (← lowerExpr value)))
    | .break => jump (isBreak := true)
    | .continue => jump (isBreak := false)
    | .ifThen condition body elseBody => do
      let operand ← lowerExpr condition
      if (← get).current.isNone then
        lowerStatements body
        if let some statements := elseBody then lowerStatements statements
        return
      let thenBlock ← newBlock
      let elseBlock ← newBlock
      terminate (.condBr operand thenBlock elseBlock)
      selectBlock thenBlock
      lowerStatements body
      match elseBody with
      | none =>
        terminate (.br elseBlock)
        selectBlock elseBlock
      | some statements =>
        let thenOpen ← suspend
        selectBlock elseBlock
        lowerStatements statements
        if thenOpen.isNone && (← get).current.isNone then return
        let continuation ← newBlock
        terminate (.br continuation)
        if let some block := thenOpen then
          selectBlock block
          terminate (.br continuation)
        selectBlock continuation
    | .forLoop initializer condition post body => do
      if let some statement := initializer then lowerStatement statement
      if (← get).current.isNone then
        if let some condition := condition then
          let _ ← lowerExpr condition
        modify fun builder => { builder with loops := ⟨none, none⟩ :: builder.loops }
        lowerStatements body
        let _ ← popLoop
        if let some statement := post then lowerStatement statement
        return
      let header ← newBlock
      let loopBody ← newBlock
      terminate (.br header)
      selectBlock header
      let exit ← match condition with
        | some condition => do
          let operand ← lowerExpr condition
          let exit ← newBlock
          terminate (.condBr operand loopBody exit)
          pure (some exit)
        | none =>
          terminate (.br loopBody)
          pure none
      selectBlock loopBody
      let continueTarget := if post.isSome then none else some header
      modify fun builder => { builder with loops := ⟨exit, continueTarget⟩ :: builder.loops }
      lowerStatements body
      jump (isBreak := false)
      let loopControl ← popLoop
      if let some statement := post then
        if let some postBlock := loopControl.continueTarget then
          selectBlock postBlock
          lowerStatement statement
          terminate (.br header)
        else
          lowerStatement statement
      if let some exit := loopControl.breakTarget then selectBlock exit

  private partial def lowerStatements (statements : Array Checked.Stmt) : LowerM Unit := do
    for statement in statements do lowerStatement statement
end

def lower (file : Checked.File) : Except Diagnostic IR.Program := do
  let mut functions := #[]
  for function in file.functions do
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
