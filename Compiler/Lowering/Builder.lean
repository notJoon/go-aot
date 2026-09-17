module

public import Compiler.IR
public import Compiler.Diagnostic

public section

namespace GoAot.Lowering

structure PendingBlock where
  instructions : Array IR.Instruction := #[]
  terminator : Option IR.Terminator := none

structure LoopContext where
  -- Targets are allocated when a live branch first needs them.
  breakTarget : Option IR.BlockId
  continueTarget : Option IR.BlockId

structure Builder where
  blocks : Array PendingBlock := #[{}]
  current : Option IR.BlockId := some 0
  nextValue : IR.ValueId := 0
  /-- Slot kinds indexed by slot ID, emitted as entry block allocations by `Builder.finish`. -/
  slots : Array IR.ValueKind := #[]
  loops : List LoopContext := []

private def builderError : Diagnostic :=
  ⟨.lowering, none, "internal error: invalid CFG builder state"⟩

def Builder.newBlock (builder : Builder) : IR.BlockId × Builder :=
  (builder.blocks.size, { builder with blocks := builder.blocks.push {} })

-- A closed path has no current block, so emitting there is a no-op rather than an error.
-- Keeping that rule here means statement lowering never repeats the reachability test.
def Builder.emit (builder : Builder) (instruction : IR.Instruction) :
    Except Diagnostic Builder := do
  let some current := builder.current | return builder
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  -- `block` above shares the instruction array with `blocks`. Pushing through it copied the whole
  -- array on every emit. `modify` takes the element out first, allowing the push to happen in place.
  let blocks := builder.blocks.modify current fun block =>
    { block with instructions := block.instructions.push instruction }
  return { builder with blocks }

def Builder.terminate (builder : Builder) (terminator : IR.Terminator) :
    Except Diagnostic Builder := do
  let some current := builder.current | return builder
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  return { builder with
    blocks := builder.blocks.set! current { block with terminator := some terminator }
    current := none }

def Builder.selectBlock (builder : Builder) (target : IR.BlockId) :
    Except Diagnostic Builder := do
  let some block := builder.blocks[target]? | throw builderError
  if builder.current.isSome || block.terminator.isSome then throw builderError
  return { builder with current := some target }

def Builder.suspend (builder : Builder) : Option IR.BlockId × Builder :=
  (builder.current, { builder with current := none })

def Builder.popLoop (builder : Builder) : Except Diagnostic (LoopContext × Builder) := do
  let context :: rest := builder.loops | throw builderError
  return (context, { builder with loops := rest })

def Builder.jump (builder : Builder) (isBreak : Bool) : Except Diagnostic Builder := do
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
def Builder.finish (builder : Builder) : Except Diagnostic (Array IR.Block) := do
  if builder.current.isSome || !builder.loops.isEmpty then throw builderError
  let blocks := builder.blocks.modify 0 fun block =>
    let allocations := builder.slots.mapIdx fun slot kind => IR.Instruction.alloca slot kind
    { block with instructions := allocations ++ block.instructions }
  blocks.mapM fun block => do
    let some terminator := block.terminator | throw builderError
    return ⟨block.instructions, terminator⟩

def Builder.emitValue (builder : Builder) (instruction : IR.ValueId → IR.Instruction) :
    Except Diagnostic (IR.Operand × Builder) := do
  -- Unlike emit, this cannot delegate: a closed path must not consume a value id, and
  -- returning `.value` would name a definition that never exists. Dead source still checks
  -- kinds, but the placeholder is discarded by emit and never enters the live CFG.
  if builder.current.isNone then return (.literal 0, builder)
  let id := builder.nextValue
  let builder ← builder.emit (instruction id)
  return (.value id, { builder with nextValue := id + 1 })

end GoAot.Lowering
