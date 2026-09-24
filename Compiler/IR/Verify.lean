module

public import Compiler.IR
import Std.Data.HashMap
import Std.Data.HashSet

public section

namespace GoAot.IR

structure VerifyError where
  message : String
  function? : Option String := none
  block? : Option BlockId := none
  instruction? : Option Nat := none
  terminator : Bool := false
  deriving Repr, BEq

def VerifyError.render (error : VerifyError) : String := Id.run do
  let mut location := ""
  if let some name := error.function? then location := s!" in function '{name}'"
  if let some block := error.block? then location := location ++ s!", block {block}"
  if let some instruction := error.instruction? then
    location := location ++ s!", instruction {instruction}"
  if error.terminator then location := location ++ ", terminator"
  return s!"internal error: invalid IR{location}: {error.message}"

@[inline] private def verifyOperand (function : Function) (values : Std.HashMap ValueId Ty)
    (expected : Ty) (operand : Operand) : Except String Unit := do
  let ty ← match operand with
    | .value id => do
      let some ty := values[id]?
        | throw s!"value {id} is not defined earlier in this block"
      pure ty
    | .literal value => do
      unless expected.isInteger do throw s!"expected {expected.name} operand"
      unless expected.contains value do
        throw s!"integer literal {value} is out of range for {expected.name}"
      pure expected
    | .floatLiteral value => do
      unless value.isFinite do throw "float literal must be finite"
      pure .float64
    | .boolLiteral _ => pure .bool
    | .argument index => do
      let some parameter := function.parameters[index]?
        | throw s!"argument index {index} is out of range"
      pure parameter.ty
  if ty != expected then throw s!"expected {expected.name} operand"

@[inline] private def verifyTarget (function : Function) (target : BlockId) : Except String Unit := do
  if target >= function.blocks.size then
    throw s!"branch target {target} is out of range"
  -- LLVM entry blocks cannot have predecessors.
  if target == 0 then
    throw "branch to entry block is not allowed"

private structure BlockState where
  definitions : Std.HashSet ValueId
  values : Std.HashMap ValueId Ty := {}
  /-- Slots declared so far in the entry block, retained when checking subsequent blocks. -/
  slots : Std.HashMap SlotId Ty := {}

private def verifyFunctions (program : Program) : Except VerifyError (Std.HashMap String Function) := do
  let mut functions : Std.HashMap String Function := {}
  for function in program.functions do
    let checked : Except String Unit := do
      unless validName function.name do
        throw s!"unsupported function name '{function.name}'"
      if functions.contains function.name then
        throw s!"duplicate function '{function.name}'"
      if function.name == "main" then
        unless function.parameters.isEmpty && function.returnKind == .void do
          throw "main must have no parameters or return value"
      let mut parameters : Std.HashSet String := {}
      for parameter in function.parameters do
        let parameter := parameter.name
        unless validName parameter do
          throw s!"unsupported parameter name '{parameter}'"
        if parameters.contains parameter then
          throw s!"duplicate parameter '{parameter}'"
        parameters := parameters.insert parameter
      if function.blocks.isEmpty then
        throw "function must have an entry block"
    checked.mapError fun message => { message, function? := some function.name }
    functions := functions.insert function.name function
  unless functions.contains "main" do throw { message := "expected main function" }
  return functions

@[inline] private def defineValue (state : BlockState) (result : ValueId)
    (ty : Ty) : Except String BlockState := do
  if state.definitions.contains result then
    throw s!"value {result} is defined more than once"
  return { state with
    definitions := state.definitions.insert result
    values := state.values.insert result ty }

@[inline] private def verifySlot (state : BlockState) (slot : SlotId)
    (ty : Ty) : Except String Unit := do
  let some declaredTy := state.slots[slot]?
    | throw s!"slot {slot} is not declared earlier in the entry block"
  if ty != declaredTy then throw s!"slot {slot} type mismatch"

@[inline] private def verifyArguments (function : Function) (values : Std.HashMap ValueId Ty)
    (callee : Function) (arguments : Array Operand) : Except String Unit := do
  if arguments.size != callee.parameters.size then
    throw s!"function '{callee.name}' expects {callee.parameters.size} arguments"
  for argument in arguments, parameter in callee.parameters do
    verifyOperand function values parameter.ty argument

@[inline] private def verifyInstruction (functions : Std.HashMap String Function)
    (function : Function) (blockIndex : BlockId) (state : BlockState)
    (instruction : Instruction) : Except String BlockState := do
  match instruction with
  | .alloca slot ty =>
    if blockIndex != 0 then throw "slots must be allocated in the entry block"
    if state.slots.contains slot then throw s!"slot {slot} is declared more than once"
    return { state with slots := state.slots.insert slot ty }
  | .load result slot ty =>
    verifySlot state slot ty
    defineValue state result ty
  | .store slot ty value =>
    verifySlot state slot ty
    verifyOperand function state.values ty value
    return state
  | .binary result op ty left right =>
    unless op.accepts ty do throw s!"operator is not defined on {ty.name}"
    verifyOperand function state.values ty left
    verifyOperand function state.values ty right
    defineValue state result (if op.isComparison then .bool else ty)
  | .shift result _ ty value countTy count =>
    unless ty.isInteger && countTy.isInteger do throw "shift operands must be integers"
    verifyOperand function state.values ty value
    verifyOperand function state.values countTy count
    defineValue state result ty
  | .convert result source target value =>
    unless source.isNumeric && target.isNumeric do
      throw s!"cannot convert {source.name} to {target.name}"
    verifyOperand function state.values source value
    defineValue state result target
  | .call result name arguments =>
    let some callee := functions[name]?
      | throw s!"unknown function '{name}'"
    let .value ty := callee.returnKind
      | throw s!"function '{name}' does not return a value"
    verifyArguments function state.values callee arguments
    defineValue state result ty
  | .callVoid name arguments =>
    let some callee := functions[name]?
      | throw s!"unknown function '{name}'"
    if name == "main" then throw "cannot call 'main'"
    if callee.returnKind != .void then
      throw s!"function '{name}' does not return void"
    verifyArguments function state.values callee arguments
    return state
  | .printString _ => return state
  | .print ty value =>
    verifyOperand function state.values ty value
    return state

@[inline] private def verifyTerminator (function : Function)
    (values : Std.HashMap ValueId Ty) (terminator : Terminator) : Except String Unit := do
  match terminator with
  | .br target => verifyTarget function target
  | .condBr condition ifTrue ifFalse =>
    verifyOperand function values .bool condition
    verifyTarget function ifTrue
    verifyTarget function ifFalse
  | .ret value =>
    match function.returnKind, value with
    | .void, none => pure ()
    | .value ty, some value => verifyOperand function values ty value
    | .void, some _ => throw "void function cannot return a value"
    | .value ty, none => throw s!"{ty.name} function must return a value"

private def verifyBlock (functions : Std.HashMap String Function) (function : Function)
    (blockIndex : BlockId) (block : Block) (previous : BlockState) : Except VerifyError BlockState := do
  let mut state := { previous with values := {} }
  for h : instructionIndex in [:block.instructions.size] do
    let instruction := block.instructions[instructionIndex]
    state ← (verifyInstruction functions function blockIndex state instruction).mapError fun message =>
      { message, function? := some function.name, block? := some blockIndex,
        instruction? := some instructionIndex }
  (verifyTerminator function state.values block.terminator).mapError fun message =>
    { message, function? := some function.name, block? := some blockIndex, terminator := true }
  return state

/--
Checks function signatures, control flow, value definitions, and operand types.
Slots must be declared once in the entry block before use, and accesses must match their types.
Slot initialization is the responsibility of lowering and is not checked here.
Returns the first error with its function, block, and instruction or terminator location.
-/
def verify (program : Program) : Except VerifyError Unit := do
  let functions ← verifyFunctions program
  for function in program.functions do
    let mut state : BlockState := { definitions := {} }
    for h : blockIndex in [:function.blocks.size] do
      state ← verifyBlock functions function blockIndex function.blocks[blockIndex] state

end GoAot.IR
