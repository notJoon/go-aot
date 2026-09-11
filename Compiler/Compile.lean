module

public import Compiler.Parser.Go

public section

namespace GoAot

namespace IR

inductive Instruction where
  | printLine (literal : String)

structure Program where
  main : Array Instruction

end IR

/--
Compile the supported Go subset to portable C.
For now, the system C compiler performs AOT codegen.
-/

private def lowerStatement : Syntax.Stmt → Except String IR.Instruction
  | .expr (.call callee (.stringLiteral literal _) _) => do
    if callee.text != "println" then
      throw s!"unknown function '{callee.text}'"
    if !literal.startsWith "\"" then
      throw "TODO: raw string literals are not supported yet"
    return .printLine literal
  | .expr _ => throw "TODO: only println with one string argument is supported"

private def lower (file : Syntax.File) : Except String IR.Program := do
  if file.packageName.text != "main" then throw "expected package main"
  let some main := file.functions[0]?
    | throw "expected exactly one main function"
  if file.functions.size != 1 || main.name.text != "main" then
    throw "expected exactly one main function"
  let mut instructions := #[]
  for statement in main.body do
    instructions := instructions.push (← lowerStatement statement)
  return ⟨instructions⟩

private def emit (program : IR.Program) : String := Id.run do
  let mut output := "#include <stdio.h>\n\nint main(void) {\n"
  for instruction in program.main do
    match instruction with
    | .printLine literal => output := output ++ "  puts(" ++ literal ++ ");\n"
  return output ++ "  return 0;\n}\n"

def compileToC (source : Source) : Except String String := do
  return emit (← lower (← parse source))

end GoAot
