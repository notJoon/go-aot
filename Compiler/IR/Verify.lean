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

@[inline] private def verifyOperand (function : Function) (values : Std.HashMap ValueId ValueKind)
    (expected : ValueKind) (operand : Operand) : Except String Unit := do
  let kind ← match operand with
    | .value id => do
      let some kind := values[id]?
        | throw s!"value {id} is not defined earlier in this block"
      pure kind
    | .literal value => do
      if value > 9223372036854775807 then
        throw "integer literal exceeds signed 64-bit range"
      pure .int
    | .argument index => do
      if index >= function.parameters.size then
        throw s!"argument index {index} is out of range"
      pure .int
  if kind != expected then
    throw (if expected == .int then "expected int operand" else "expected bool operand")

@[inline] private def verifyTarget (function : Function) (target : BlockId) : Except String Unit := do
  if target >= function.blocks.size then
    throw s!"branch target {target} is out of range"
  -- LLVM entry blocks cannot have predecessors.
  if target == 0 then
    throw "branch to entry block is not allowed"

private structure BlockState where
  definitions : Std.HashSet ValueId
  values : Std.HashMap ValueId ValueKind := {}

def verify (program : Program) : Except VerifyError Unit := do
  let mut functions : Std.HashMap String Function := {}
  for function in program.functions do
    let location : VerifyError := { message := "", function? := some function.name }
    unless validName function.name do
      throw { location with message := s!"unsupported function name '{function.name}'" }
    if functions.contains function.name then
      throw { location with message := s!"duplicate function '{function.name}'" }
    functions := functions.insert function.name function
    if function.name == "main" then
      unless function.parameters.isEmpty && function.returnKind == .void do
        throw { location with message := "main must have no parameters or return value" }
    else if function.returnKind != .int then
      throw { location with message := s!"function '{function.name}' must return int" }
    let mut parameters : Array String := #[]
    for parameter in function.parameters do
      unless validName parameter do
        throw { location with message := s!"unsupported parameter name '{parameter}'" }
      if parameters.contains parameter then
        throw { location with message := s!"duplicate parameter '{parameter}'" }
      parameters := parameters.push parameter
    if function.blocks.isEmpty then
      throw { location with message := "function must have an entry block" }
  unless functions.contains "main" do throw { message := "expected main function" }
  for function in program.functions do
    let mut definitions : Std.HashSet ValueId := {}
    for h : blockIndex in [:function.blocks.size] do
      let block := function.blocks[blockIndex]
      -- One loop state avoids repacking both maps after instructions that define no value.
      let mut state : BlockState := { definitions }
      for h : instructionIndex in [:block.instructions.size] do
        let instruction := block.instructions[instructionIndex]
        let checked : Except String Unit := do
          match instruction with
          | .binary _ _ left right =>
            verifyOperand function state.values .int left
            verifyOperand function state.values .int right
          | .call _ name arguments =>
            let some callee := functions[name]?
              | throw s!"unknown function '{name}'"
            if callee.returnKind != .int then
              throw s!"function '{name}' does not return int"
            if arguments.size != callee.parameters.size then
              throw s!"function '{name}' expects {callee.parameters.size} arguments"
            for argument in arguments do verifyOperand function state.values .int argument
          | .printString _ => pure ()
          | .printInt value => verifyOperand function state.values .int value
        checked.mapError fun message =>
          { message, function? := some function.name, block? := some blockIndex,
            instruction? := some instructionIndex }
        match instruction with
        | .binary result .. | .call result .. =>
          if state.definitions.contains result then
            throw {
              message := s!"value {result} is defined more than once"
              function? := some function.name, block? := some blockIndex,
              instruction? := some instructionIndex }
          let kind := match instruction with
            | .binary _ .less .. => .bool
            | _ => .int
          state := {
            definitions := state.definitions.insert result
            values := state.values.insert result kind }
        | _ => pure ()
      definitions := state.definitions
      let checked : Except String Unit := do
        match block.terminator with
        | .br target => verifyTarget function target
        | .condBr condition ifTrue ifFalse =>
          verifyOperand function state.values .bool condition
          verifyTarget function ifTrue
          verifyTarget function ifFalse
        | .ret value =>
          match function.returnKind, value with
          | .void, none => pure ()
          | .int, some value => verifyOperand function state.values .int value
          | .void, some _ => throw "void function cannot return a value"
          | .int, none => throw "int function must return a value"
      checked.mapError fun message =>
        { message, function? := some function.name, block? := some blockIndex, terminator := true }

end GoAot.IR
