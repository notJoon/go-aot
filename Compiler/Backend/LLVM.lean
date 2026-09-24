module

public import Compiler.IR
import Compiler.Backend.Symbol
import Std.Data.HashMap

public section

namespace GoAot.Backend.LLVM

-- Collect declarations and deduplicate string globals before any function is emitted.
private def collectRuntimeNeeds (program : IR.Program) :
    Array ByteArray × Std.HashMap ByteArray Nat × Bool × Bool := Id.run do
  let mut result := #[]
  let mut indices : Std.HashMap ByteArray Nat := {}
  let mut needsIntFormat := false
  let mut needsDivide := false
  for function in program.functions do
    for block in function.blocks do
      for instruction in block.instructions do
        match instruction with
        | .printString bytes =>
          unless indices.contains bytes do
            indices := indices.insert bytes result.size
            result := result.push bytes
        | .printInt _ => needsIntFormat := true
        | .binary _ .divide .. | .binary _ .remainder .. => needsDivide := true
        | _ => pure ()
  return (result, indices, needsIntFormat, needsDivide)

private def emitBytes (output : String) (bytes : ByteArray) : String := Id.run do
  let mut output := output
  for byte in bytes do
    let value := byte.toNat
    if 32 <= value && value <= 126 && value != 34 && value != 92 then
      output := output.push (Char.ofNat value)
    else
      output := (output.push '\\').push (value / 16).digitChar.toUpper
      output := output.push (value % 16).digitChar.toUpper
  return output

private def llvmType : IR.ValueKind → String
  | .int => "i64"
  | .bool => "i1"

private def emitOperand (output : String) : IR.Operand → String
  | .value id => output ++ "%v" ++ toString id
  | .literal value => output ++ toString value
  | .boolLiteral value => output ++ (if value then "true" else "false")
  | .argument index => output ++ "%arg" ++ toString index

private def emitArguments (output : String) (callee : Option IR.Function)
    (arguments : Array IR.Operand) : String := Id.run do
  let kinds := (callee.map (·.parameters.map (·.kind))).getD #[]
  let mut output := output ++ "("
  for h : index in [:arguments.size] do
    if index != 0 then output := output ++ ", "
    output := emitOperand (output ++ llvmType (kinds[index]?.getD .int) ++ " ") arguments[index]
  return output ++ ")\n"

private def emitInstructions (functions : Std.HashMap String IR.Function)
    (stringIndices : Std.HashMap ByteArray Nat)
    (output : String) (instructions : Array IR.Instruction) : String := Id.run do
  let mut output := output
  for instruction in instructions do
    match instruction with
    | .alloca slot kind =>
      output := output ++ s!"  %slot{slot} = alloca {llvmType kind}\n"
    | .load id slot kind =>
      output := output ++ s!"  %v{id} = load {llvmType kind}, ptr %slot{slot}\n"
    | .store slot kind value =>
      output := emitOperand (output ++ s!"  store {llvmType kind} ") value ++
        s!", ptr %slot{slot}\n"
    | .binary id op kind left right =>
      output := output ++ "  %v" ++ toString id ++ " = "
      let helper? := match op with
        | .divide => some "@goaot.div" | .remainder => some "@goaot.rem" | _ => none
      if let some helper := helper? then
        output := emitOperand (output ++ "call i64 " ++ helper ++ "(i64 ") left
        output := emitOperand (output ++ ", i64 ") right ++ ")\n"
      else
        let operation := match op with
          | .add => "add" | .subtract => "sub" | .multiply => "mul"
          | .equal => "icmp eq" | .notEqual => "icmp ne"
          | .less => "icmp slt" | .lessEqual => "icmp sle"
          | .greater => "icmp sgt" | .greaterEqual => "icmp sge"
          | .divide => "sdiv" | .remainder => "srem"
        output := emitOperand (output ++ operation ++ " " ++ llvmType kind ++ " ") left
        output := emitOperand (output ++ ", ") right ++ "\n"
    | .call id name arguments =>
      let callee := functions[name]?
      let result := match callee.map (·.returnKind) with
        | some (.value kind) => llvmType kind
        | _ => "i64"
      output := output ++ "  %v" ++ toString id ++ " = call " ++ result ++ " @" ++ Symbol.function name
      output := emitArguments output callee arguments
    | .callVoid name arguments =>
      output := emitArguments (output ++ "  call void @" ++ Symbol.function name) functions[name]? arguments
    | .printString bytes =>
      let index := stringIndices[bytes]!
      output := output ++ "  call void @goaot.print_line(ptr @.str." ++ toString index ++
        ", i64 " ++ toString bytes.size ++ ")\n"
    | .printInt value =>
      output := emitOperand (output ++ "  call i32 (ptr, ...) @printf(ptr @.int_format, i64 ") value ++ ")\n"
  return output

private def resultType (function : IR.Function) : String :=
  match function.returnKind with
  | .value kind => llvmType kind
  | .void => if Symbol.isEntry function then "i32" else "void"

private def emitTerminator (function : IR.Function) (output : String) : IR.Terminator → String
  | .br target => output ++ "  br label %bb" ++ toString target ++ "\n"
  | .condBr condition ifTrue ifFalse =>
    emitOperand (output ++ "  br i1 ") condition ++ ", label %bb" ++ toString ifTrue ++
      ", label %bb" ++ toString ifFalse ++ "\n"
  | .ret none =>
    if Symbol.returnsVoid function then output ++ "  ret void\n"
    else output ++ "  ret " ++ resultType function ++ " 0\n"
  | .ret (some value) => emitOperand (output ++ "  ret " ++ resultType function ++ " ") value ++ "\n"

private def emitFunction (functions : Std.HashMap String IR.Function)
    (stringIndices : Std.HashMap ByteArray Nat) (output : String)
    (function : IR.Function) : String := Id.run do
  let linkage := if Symbol.isEntry function then "" else "internal "
  let mut output := output ++ "define " ++ linkage ++ resultType function ++ " @" ++ Symbol.function function.name ++ "("
  for h : index in [:function.parameters.size] do
    if index != 0 then output := output ++ ", "
    output := output ++ llvmType function.parameters[index].kind ++ " %arg" ++ toString index
  output := output ++ ") {\n"
  for h : index in [:function.blocks.size] do
    let block := function.blocks[index]
    if index != 0 then output := output ++ "\n"
    output := output ++ "bb" ++ toString index ++ ":\n"
    output := emitInstructions functions stringIndices output block.instructions
    output := emitTerminator function output block.terminator
  return output ++ "}\n"

def emit (program : IR.Program) : String := Id.run do
  let (strings, stringIndices, needsIntFormat, needsDivide) := collectRuntimeNeeds program
  let needsWrite := !strings.isEmpty || needsDivide
  -- Verified IR names every callee, so call sites can take their types from its signature.
  let functions := program.functions.foldl (fun map function => map.insert function.name function) {}

  let mut output := ""
  for h : i in [:strings.size] do
    let bytes := strings[i]
    output := emitBytes (output ++ "@.str." ++ toString i ++ " = private unnamed_addr constant [" ++
      toString (bytes.size + 1) ++ " x i8] c\"") bytes ++ "\\00\"\n"
  if needsIntFormat then
    output := output ++ "@.int_format = private unnamed_addr constant [6 x i8] c\"%lld\\0A\\00\"\n"
  if needsDivide then output := output ++
    "@.divide_message = private unnamed_addr constant [45 x i8] " ++
    "c\"panic: runtime error: integer divide by zero\\0A\"\n"
  if needsWrite || needsIntFormat then output := output ++ "\n"
  if needsWrite then
    output := output ++ "declare i32 @fflush(ptr)\ndeclare i64 @write(i32, ptr, i64)\n"
  if needsIntFormat then output := output ++ "declare i32 @printf(ptr, ...)\n"
  if needsDivide then output := output ++ "declare void @exit(i32)\n"
  if needsWrite || needsIntFormat then output := output ++ "\n"
  -- Darwin exposes `__stdoutp` so `stdout` is not a portable linkable symbol.
  if !strings.isEmpty then output := output ++
    "define internal void @goaot.print_line(ptr %bytes, i64 %length) {\n" ++
    "entry:\n  %newline = alloca i8\n  store i8 10, ptr %newline\n" ++
    "  call i32 @fflush(ptr null)\n  br label %loop\n\nloop:\n" ++
    "  %offset = phi i64 [ 0, %entry ], [ %next, %body ]\n" ++
    "  %done = icmp eq i64 %offset, %length\n" ++
    "  br i1 %done, label %exit, label %body\n\nbody:\n" ++
    "  %address = getelementptr i8, ptr %bytes, i64 %offset\n" ++
    "  %remaining = sub i64 %length, %offset\n" ++
    "  %written = call i64 @write(i32 1, ptr %address, i64 %remaining)\n" ++
    "  %next = add i64 %offset, %written\n  %failed = icmp slt i64 %written, 1\n" ++
    "  br i1 %failed, label %exit, label %loop\n\n" ++
    "exit:\n  call i64 @write(i32 1, ptr %newline, i64 1)\n  ret void\n}\n\n"
  -- Go panics with exit status 2. The most negative value divided by -1 wraps, where `sdiv`
  -- and `srem` are undefined.
  if needsDivide then output := output ++
    "define internal void @goaot.panic_divide() {\n" ++
    "  call i32 @fflush(ptr null)\n" ++
    "  call i64 @write(i32 2, ptr @.divide_message, i64 45)\n" ++
    "  call void @exit(i32 2)\n  unreachable\n}\n\n" ++
    "define internal i64 @goaot.div(i64 %a, i64 %b) {\n" ++
    "entry:\n  %zero = icmp eq i64 %b, 0\n  br i1 %zero, label %panic, label %check\n\n" ++
    "panic:\n  call void @goaot.panic_divide()\n  unreachable\n\n" ++
    "check:\n  %negate = icmp eq i64 %b, -1\n  br i1 %negate, label %wrap, label %divide\n\n" ++
    "wrap:\n  %negated = sub i64 0, %a\n  ret i64 %negated\n\n" ++
    "divide:\n  %quotient = sdiv i64 %a, %b\n  ret i64 %quotient\n}\n\n" ++
    "define internal i64 @goaot.rem(i64 %a, i64 %b) {\n" ++
    "entry:\n  %zero = icmp eq i64 %b, 0\n  br i1 %zero, label %panic, label %check\n\n" ++
    "panic:\n  call void @goaot.panic_divide()\n  unreachable\n\n" ++
    "check:\n  %negate = icmp eq i64 %b, -1\n  br i1 %negate, label %wrap, label %divide\n\n" ++
    "wrap:\n  ret i64 0\n\n" ++
    "divide:\n  %remainder = srem i64 %a, %b\n  ret i64 %remainder\n}\n\n"
  for h : index in [:program.functions.size] do
    if index != 0 then output := output ++ "\n"
    output := emitFunction functions stringIndices output program.functions[index]
  return output

end GoAot.Backend.LLVM
