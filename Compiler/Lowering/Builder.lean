module

public import Compiler.IR
public import Compiler.Diagnostic

public section

namespace GoAot.Lowering

structure PendingBlock where
  instructions : Array IR.Instruction := #[]
  terminator : Option IR.Terminator := none
  deriving Inhabited

structure LoopContext where
  breakTarget : IR.BlockId
  continueTarget : IR.BlockId

structure Builder where
  blocks : Array PendingBlock := #[{}]
  current : Option IR.BlockId := some 0
  nextValue : IR.ValueId := 0
  slots : Array IR.ValueKind := #[]
  loops : List LoopContext := []

private def builderError : Diagnostic :=
  ⟨.lowering, none, "internal error: invalid CFG builder state"⟩

def Builder.newBlock (builder : Builder) : IR.BlockId × Builder :=
  (builder.blocks.size, { builder with blocks := builder.blocks.push {} })

def Builder.selectBlock (builder : Builder) (target : IR.BlockId) :
    Except Diagnostic Builder := do
  let some block := builder.blocks[target]? | throw builderError
  if builder.current.isSome || block.terminator.isSome then throw builderError
  return { builder with current := some target }

/-- Select a fresh unconnected block only when the previous source path has ended. -/
@[inline] def Builder.startStatement (builder : Builder) : Except Diagnostic Builder := do
  if builder.current.isSome then return builder
  let (target, builder) := builder.newBlock
  builder.selectBlock target

def Builder.emit (builder : Builder) (instruction : IR.Instruction) :
    Except Diagnostic Builder := do
  let some current := builder.current | throw builderError
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  -- Updating inside `modify` avoids copying the instruction array on each append.
  let blocks := builder.blocks.modify current fun block =>
    { block with instructions := block.instructions.push instruction }
  return { builder with blocks }

def Builder.terminate (builder : Builder) (terminator : IR.Terminator) :
    Except Diagnostic Builder := do
  let some current := builder.current | throw builderError
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  return { builder with
    blocks := builder.blocks.set! current { block with terminator := some terminator }
    current := none }

/-- Connect an open path to `target`, leaving a terminated path untouched. -/
def Builder.branchIfOpen (builder : Builder) (target : IR.BlockId) :
    Except Diagnostic Builder := do
  if builder.current.isNone then return builder
  builder.terminate (.br target)

def Builder.popLoop (builder : Builder) : Except Diagnostic (LoopContext × Builder) := do
  let context :: rest := builder.loops | throw builderError
  return (context, { builder with loops := rest })

def Builder.jump (builder : Builder) (isBreak : Bool) : Except Diagnostic Builder := do
  let context :: _ := builder.loops | throw builderError
  builder.terminate (.br (if isBreak then context.breakTarget else context.continueTarget))

def Builder.emitValue (builder : Builder) (instruction : IR.ValueId → IR.Instruction) :
    Except Diagnostic (IR.Operand × Builder) := do
  let id := builder.nextValue
  let builder ← builder.emit (instruction id)
  return (.value id, { builder with nextValue := id + 1 })

/-- Keep entry reachable blocks in their existing order and renumber their branches.
Unreachable blocks may be unterminated. Value IDs remain unchanged. -/
def Builder.finish (builder : Builder) : Except Diagnostic (Array IR.Block) := do
  unless builder.loops.isEmpty do throw builderError
  let mut visited := Array.replicate builder.blocks.size false
  let mut work := [0]
  while let target :: rest := work do
    work := rest
    unless target < builder.blocks.size do throw builderError
    if visited[target]! then continue
    visited := visited.set! target true
    let some terminator := builder.blocks[target]!.terminator | throw builderError
    match terminator with
    | .br next => work := next :: work
    | .condBr _ yes no => work := yes :: no :: work
    | .ret _ => pure ()
  let mut numbering := Array.replicate builder.blocks.size (none : Option IR.BlockId)
  let mut count := 0
  for i in [:builder.blocks.size] do
    if visited[i]! then
      numbering := numbering.set! i (some count)
      count := count + 1
  let remap (target : IR.BlockId) : Except Diagnostic IR.BlockId :=
    match numbering[target]? with
    | some (some next) => pure next
    | _ => throw builderError
  let mut blocks := Array.emptyWithCapacity count
  for i in [:builder.blocks.size] do
    if visited[i]! then
      let block := builder.blocks[i]!
      let some terminator := block.terminator | throw builderError
      let terminator ← match terminator with
        | .br target => .br <$> remap target
        | .condBr operand yes no => .condBr operand <$> remap yes <*> remap no
        | .ret value => pure (.ret value)
      let instructions := if i == 0 then
        (builder.slots.mapIdx fun slot kind => IR.Instruction.alloca slot kind) ++ block.instructions
        else block.instructions
      blocks := blocks.push ⟨instructions, terminator⟩
  return blocks

end GoAot.Lowering
