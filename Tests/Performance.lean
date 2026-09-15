import Compiler.Lowering
import Compiler.IR.Verify
import Compiler.Backend.LLVM

open GoAot

private def verificationProgram (count : Nat) : IR.Program :=
  let instructions := Array.replicate count (IR.Instruction.printInt (.literal 1))
  ⟨#[⟨"main", #[], .void, #[⟨instructions, .ret none⟩]⟩]⟩

@[noinline] private def verificationAllocations (program : IR.Program) : IO Nat := do
  IO.setNumHeartbeats 0
  let result := IR.verify program
  unless result.toBool do throw (IO.userError "allocation probe rejected valid IR")
  IO.getNumHeartbeats

@[noinline] private def emissionAllocations (program : IR.Program) : IO Nat := do
  IO.setNumHeartbeats 0
  if (Backend.LLVM.emit program).isEmpty then throw (IO.userError "emitter produced no output")
  IO.getNumHeartbeats

private def bytesProgram (count : Nat) : IR.Program :=
  ⟨#[⟨"main", #[], .void,
    #[⟨#[.printString ⟨Array.replicate count 97⟩], .ret none⟩]⟩]⟩

private def functionSource (count : Nat) : Source := Source.ofString <| Id.run do
  let mut text := "package main\nfunc main() { println(f0()) }\n"
  for index in [:count] do
    text := text ++ s!"func f{index}() int " ++ "{ return " ++
      (if index + 1 == count then "1" else s!"f{index + 1}()") ++ " }\n"
  return text

@[noinline] private def measureFunctions (file : Syntax.File) : IO Unit := do
  let start ← IO.monoNanosNow
  let .ok program := Lowering.lower file | throw (IO.userError "function probe failed to lower")
  let lowered ← IO.monoNanosNow
  let .ok () := IR.verify program | throw (IO.userError "function probe failed verification")
  let verified ← IO.monoNanosNow
  IO.println s!"{file.functions.size} functions: lower {(lowered - start) / 1000} µs, verify {(verified - lowered) / 1000} µs"

@[noinline] private def loweringAllocations (file : Syntax.File) : IO Nat := do
  IO.setNumHeartbeats 0
  unless (Lowering.lower file).toBool do throw (IO.userError "literal probe failed to lower")
  IO.getNumHeartbeats

private def literalAllocations (count : Nat) : IO Nat := do
  let source := Source.ofString ("package main\nfunc main() {" ++
    String.join (List.replicate count "println(1);") ++ "}\n")
  let .ok file := parse source | throw (IO.userError "literal probe failed to parse")
  loweringAllocations file

@[noinline] private def nameAllocations (name : String) : IO Nat := do
  IO.setNumHeartbeats 0
  unless IR.validName name do throw (IO.userError "name probe rejected a valid name")
  IO.getNumHeartbeats

def performanceMain : IO Unit := do
  let small := 10
  let large := 10000
  let short ← verificationAllocations (verificationProgram small)
  let long ← verificationAllocations (verificationProgram large)
  IO.println s!"Verification allocations: {short} -> {long}"
  unless long <= short do
    throw (IO.userError "verification allocates per instruction without value definitions")
  let short ← emissionAllocations (bytesProgram small)
  let long ← emissionAllocations (bytesProgram large)
  IO.println s!"LLVM byte allocations: {short} -> {long}"
  unless long <= short + 4 do
    throw (IO.userError "LLVM emission allocates per byte")
  for count in [1000, 3000] do
    let .ok file := parse (functionSource count) | throw (IO.userError "function probe failed to parse")
    measureFunctions file
  let short ← nameAllocations (String.ofList (List.replicate small 'a'))
  let long ← nameAllocations (String.ofList (List.replicate large 'a'))
  IO.println s!"Name allocations: {short} -> {long}"
  unless long <= short do throw (IO.userError "name validation allocates per character")
  let short ← literalAllocations small
  let long ← literalAllocations large
  IO.println s!"Lowering literal allocations: {short} -> {long}"
  unless long <= short + 8 * (large - small) do
    throw (IO.userError "lowering exceeds eight allocations per literal statement")
