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

private def verifyOperand (function : Function) (values : Std.HashMap ValueId ValueKind)
    (location : VerifyError) (expected : ValueKind) (operand : Operand) : Except VerifyError Unit := do
  let kind ← match operand with
    | .value id => do
      let some kind := values[id]?
        | throw { location with message := s!"value {id} is not defined earlier in this block" }
      pure kind
    | .literal value => do
      if value > 9223372036854775807 then
        throw { location with message := "integer literal exceeds signed 64-bit range" }
      pure .int
    | .argument index => do
      if index >= function.parameters.size then
        throw { location with message := s!"argument index {index} is out of range" }
      pure .int
  if kind != expected then
    throw { location with message := if expected == .int then "expected int operand" else "expected bool operand" }

private def verifyTarget (function : Function) (location : VerifyError)
    (target : BlockId) : Except VerifyError Unit := do
  if target >= function.blocks.size then
    throw { location with message := s!"branch target {target} is out of range" }
  -- LLVM entry blocks cannot have predecessors.
  if target == 0 then
    throw { location with message := "branch to entry block is not allowed" }

def verify (program : Program) : Except VerifyError Unit := do
  let mut names : Array String := #[]
  for function in program.functions do
    let location : VerifyError := { message := "", function? := some function.name }
    unless validName function.name do
      throw { location with message := s!"unsupported function name '{function.name}'" }
    if names.contains function.name then
      throw { location with message := s!"duplicate function '{function.name}'" }
    names := names.push function.name
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
  unless names.contains "main" do throw { message := "expected main function" }
  for function in program.functions do
    let mut definitions : Std.HashSet ValueId := {}
    for (block, blockIndex) in function.blocks.zipIdx do
      let location : VerifyError :=
        { message := "", function? := some function.name, block? := some blockIndex }
      let mut values : Std.HashMap ValueId ValueKind := {}
      for (instruction, instructionIndex) in block.instructions.zipIdx do
        let location := { location with instruction? := some instructionIndex }
        let result? ← match instruction with
          | .binary result op left right => do
            verifyOperand function values location .int left
            verifyOperand function values location .int right
            pure (some (result, match op with | .less => .bool | _ => .int))
          | .call result name arguments => do
            let some callee := program.functions.find? (·.name == name)
              | throw { location with message := s!"unknown function '{name}'" }
            if callee.returnKind != .int then
              throw { location with message := s!"function '{name}' does not return int" }
            if arguments.size != callee.parameters.size then
              throw { location with message := s!"function '{name}' expects {callee.parameters.size} arguments" }
            for argument in arguments do verifyOperand function values location .int argument
            pure (some (result, .int))
          | .printString _ => pure none
          | .printInt value => do
            verifyOperand function values location .int value
            pure none
        if let some (result, kind) := result? then
          if definitions.contains result then
            throw { location with message := s!"value {result} is defined more than once" }
          definitions := definitions.insert result
          values := values.insert result kind
      let location := { location with terminator := true }
      match block.terminator with
      | .br target => verifyTarget function location target
      | .condBr condition ifTrue ifFalse =>
        verifyOperand function values location .bool condition
        verifyTarget function location ifTrue
        verifyTarget function location ifFalse
      | .ret value =>
        match function.returnKind, value with
        | .void, none => pure ()
        | .int, some value => verifyOperand function values location .int value
        | .void, some _ => throw { location with message := "void function cannot return a value" }
        | .int, none => throw { location with message := "int function must return a value" }

end GoAot.IR
