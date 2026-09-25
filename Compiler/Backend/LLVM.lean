module

public import Compiler.IR
import Compiler.Backend.LLVM.Runtime
import Compiler.Backend.Symbol
import Std.Data.HashMap

public section

namespace GoAot.Backend.LLVM

/-- No results is `void`, one is its type, and several are an anonymous struct of their types. -/
private def resultsType (types : Array Ty) : String :=
  match types with
  | #[] => "void"
  | #[ty] => llvmType ty
  | _ => "{ " ++ ", ".intercalate (types.map llvmType).toList ++ " }"

private def hexDigits (value count : Nat) : String :=
  String.ofList ((List.range count).reverse.map fun index => (value / 16 ^ index % 16).digitChar.toUpper)

-- LLVM reads integer constants in the signed range of their width, and doubles as their bits.
private def emitOperand (output : String) (ty : Ty) : IR.Operand → String
  | .value id => output ++ "%v" ++ toString id
  | .literal value =>
    let modulus : Int := (2 ^ ty.bits : Nat)
    let value := value % modulus
    output ++ toString (if value ≥ modulus / 2 then value - modulus else value)
  | .floatLiteral value => output ++ "0x" ++ hexDigits value.toBits.toNat 16
  | .boolLiteral value => output ++ (if value then "true" else "false")
  | .argument index => output ++ "%arg" ++ toString index

private def emitArguments (output : String) (callee : Option IR.Function)
    (arguments : Array IR.Operand) : String := Id.run do
  let types := (callee.map (·.parameters.map (·.ty))).getD #[]
  let mut output := output ++ "("
  for h : index in [:arguments.size] do
    if index != 0 then output := output ++ ", "
    let ty := types[index]?.getD .int
    output := emitOperand (output ++ llvmType ty ++ " ") ty arguments[index]
  return output ++ ")\n"

private def emitBinary (output : String) (id : IR.ValueId) (op : Op) (ty : Ty)
    (left right : IR.Operand) : String :=
  let name := "%v" ++ toString id
  let type := llvmType ty
  if (op == .divide || op == .remainder) && ty.isInteger then
    -- Narrow operands widen to i64, so one helper per signedness covers every width.
    let helper := "@goaot." ++ (if ty.isSigned then "" else "u") ++ (if op == .divide then "div" else "rem")
    if ty.bits == 64 then
      emitOperand (emitOperand (output ++ "  " ++ name ++ " = call i64 " ++ helper ++ "(i64 ") ty left ++
        ", i64 ") ty right ++ ")\n"
    else
      let extend := if ty.isSigned then "sext " else "zext "
      let output := emitOperand (output ++ "  " ++ name ++ ".a = " ++ extend ++ type ++ " ") ty left ++
        " to i64\n"
      let output := emitOperand (output ++ "  " ++ name ++ ".b = " ++ extend ++ type ++ " ") ty right ++
        " to i64\n"
      output ++ "  " ++ name ++ ".wide = call i64 " ++ helper ++ "(i64 " ++ name ++ ".a, i64 " ++
        name ++ ".b)\n  " ++ name ++ " = trunc i64 " ++ name ++ ".wide to " ++ type ++ "\n"
  else
    let operation := match ty.kind, op with
      | .float, .add => "fadd" | .float, .subtract => "fsub" | .float, .multiply => "fmul"
      | .float, .divide => "fdiv" | .float, .remainder => "frem"
      | .float, .equal => "fcmp oeq" | .float, .notEqual => "fcmp une"
      | .float, .less => "fcmp olt" | .float, .lessEqual => "fcmp ole"
      | .float, .greater => "fcmp ogt" | .float, .greaterEqual => "fcmp oge"
      | _, .add => "add" | _, .subtract => "sub" | _, .multiply => "mul"
      | _, .divide => "sdiv" | _, .remainder => "srem"
      | _, .bitAnd => "and" | _, .bitOr => "or" | _, .bitXor => "xor"
      | _, .equal => "icmp eq" | _, .notEqual => "icmp ne"
      | .unsigned, .less => "icmp ult" | .unsigned, .lessEqual => "icmp ule"
      | .unsigned, .greater => "icmp ugt" | .unsigned, .greaterEqual => "icmp uge"
      | _, .less => "icmp slt" | _, .lessEqual => "icmp sle"
      | _, .greater => "icmp sgt" | _, .greaterEqual => "icmp sge"
    emitOperand (emitOperand (output ++ "  " ++ name ++ " = " ++ operation ++ " " ++ type ++ " ") ty left ++
      ", ") ty right ++ "\n"

-- `shl`, `lshr`, and `ashr` are poison for a count at or above the width, so the count is
-- clamped first and the Go result for large counts selected afterwards.
private def emitShift (output : String) (id : IR.ValueId) (op : ShiftOp) (ty : Ty)
    (value : IR.Operand) (countTy : Ty) (count : IR.Operand) : String := Id.run do
  let name := "%v" ++ toString id
  let type := llvmType ty
  let mut output := output
  let mut wide := emitOperand "" countTy count
  if countTy.bits < 64 then
    output := output ++ "  " ++ name ++ ".count = " ++ (if countTy.isSigned then "sext " else "zext ") ++
      llvmType countTy ++ " " ++ wide ++ " to i64\n"
    wide := name ++ ".count"
  if countTy.isSigned then output := output ++ "  call void @goaot.check_shift(i64 " ++ wide ++ ")\n"
  output := output ++ "  " ++ name ++ ".big = icmp uge i64 " ++ wide ++ ", " ++ toString ty.bits ++ "\n"
  output := output ++ "  " ++ name ++ ".clamped = select i1 " ++ name ++ ".big, i64 " ++
    toString (ty.bits - 1) ++ ", i64 " ++ wide ++ "\n"
  let mut amount := name ++ ".clamped"
  if ty.bits < 64 then
    output := output ++ "  " ++ name ++ ".amount = trunc i64 " ++ amount ++ " to " ++ type ++ "\n"
    amount := name ++ ".amount"
  match op, ty.isSigned with
  | .right, true =>
    return emitOperand (output ++ "  " ++ name ++ " = ashr " ++ type ++ " ") ty value ++ ", " ++ amount ++ "\n"
  | _, _ =>
    let operation := if op == .left then "shl" else "lshr"
    output := emitOperand (output ++ "  " ++ name ++ ".raw = " ++ operation ++ " " ++ type ++ " ") ty value ++
      ", " ++ amount ++ "\n"
    return output ++ "  " ++ name ++ " = select i1 " ++ name ++ ".big, " ++ type ++ " 0, " ++ type ++ " " ++
      name ++ ".raw\n"

private def emitConvert (output : String) (id : IR.ValueId) (source target : Ty)
    (value : IR.Operand) : String :=
  let head := output ++ "  %v" ++ toString id ++ " = "
  let sourceType := llvmType source
  let targetType := llvmType target
  match source.kind, target.kind with
  | .float, .signed | .float, .unsigned =>
    let wide := IR.floatConversionTy target
    let wideType := llvmType wide
    let name := "%v" ++ toString id
    let call := "call " ++ wideType ++ " @llvm.fpto" ++ (if wide.isSigned then "s" else "u") ++ "i.sat." ++
      wideType ++ ".f64(double "
    if wide == target then emitOperand (head ++ call) source value ++ ")\n"
    else
      emitOperand (output ++ "  " ++ name ++ ".wide = " ++ call) source value ++ ")\n  " ++ name ++
        " = trunc " ++ wideType ++ " " ++ name ++ ".wide to " ++ targetType ++ "\n"
  | _, .float =>
    emitOperand (head ++ (if source.isSigned then "sitofp " else "uitofp ") ++ sourceType ++ " ") source value ++
      " to double\n"
  | _, _ =>
    let operation := if source.bits > target.bits then "trunc"
      else if source.bits < target.bits then (if source.isSigned then "sext" else "zext")
      else "bitcast"
    emitOperand (head ++ operation ++ " " ++ sourceType ++ " ") source value ++ " to " ++ targetType ++ "\n"

private def emitPrint (output : String) (temporary : String) (ty : Ty) (value : IR.Operand) : String :=
  match ty.kind with
  | .bool =>
    emitOperand (output ++ "  " ++ temporary ++ " = select i1 ") ty value ++
      ", ptr @.true, ptr @.false\n  call i32 @puts(ptr " ++ temporary ++ ")\n"
  | .float => emitOperand (output ++ "  call void @goaot.print_float(double ") ty value ++ ")\n"
  | kind =>
    let format := if kind == .signed then "@.int_format" else "@.uint_format"
    let (output, wide) := if ty.bits == 64 then (output, emitOperand "" ty value)
      else (emitOperand (output ++ "  " ++ temporary ++ " = " ++ (if kind == .signed then "sext " else "zext ") ++
        llvmType ty ++ " ") ty value ++ " to i64\n", temporary)
    output ++ "  call i32 (ptr, ...) @printf(ptr " ++ format ++ ", i64 " ++ wide ++ ")\n"

private def emitInstructions (functions : Std.HashMap String IR.Function)
    (stringIndices : Std.HashMap ByteArray Nat) (blockIndex : Nat)
    (output : String) (instructions : Array IR.Instruction) : String := Id.run do
  let mut output := output
  for h : index in [:instructions.size] do
    match instructions[index] with
    | .alloca slot ty =>
      output := output ++ s!"  %slot{slot} = alloca {llvmType ty}\n"
    | .load id slot ty =>
      output := output ++ s!"  %v{id} = load {llvmType ty}, ptr %slot{slot}\n"
    | .store slot ty value =>
      output := emitOperand (output ++ s!"  store {llvmType ty} ") ty value ++ s!", ptr %slot{slot}\n"
    | .binary id op ty left right => output := emitBinary output id op ty left right
    | .shift id op ty value countTy count => output := emitShift output id op ty value countTy count
    | .convert id source target value => output := emitConvert output id source target value
    | .call results name arguments =>
      let callee := functions[name]?
      let types := (callee.map (·.results)).getD #[]
      let type := resultsType types
      -- Several results arrive as one struct, taken apart with `extractvalue`.
      let holder := s!"%results{results[0]?.getD 0}"
      output := output ++ "  " ++ (match results with
        | #[] => ""
        | #[id] => s!"%v{id} = "
        | _ => holder ++ " = ") ++ "call " ++ type ++ " " ++ Symbol.function name
      output := emitArguments output callee arguments
      if results.size ≥ 2 then
        for h : index in [:results.size] do
          output := output ++ s!"  %v{results[index]} = extractvalue {type} {holder}, {index}\n"
    | .printString bytes =>
      let index := stringIndices[bytes]!
      output := output ++ "  call void @goaot.print_line(ptr @.str." ++ toString index ++
        ", i64 " ++ toString bytes.size ++ ")\n"
    | .print ty value => output := emitPrint output s!"%print{blockIndex}.{index}" ty value
  return output

private def resultType (function : IR.Function) : String :=
  if Symbol.isEntry function then "i32" else resultsType function.results

private def emitTerminator (function : IR.Function) (blockIndex : Nat) (output : String) :
    IR.Terminator → String
  | .br target => output ++ "  br label %bb" ++ toString target ++ "\n"
  | .condBr condition ifTrue ifFalse =>
    emitOperand (output ++ "  br i1 ") .bool condition ++ ", label %bb" ++ toString ifTrue ++
      ", label %bb" ++ toString ifFalse ++ "\n"
  | .ret #[] =>
    if Symbol.returnsVoid function then output ++ "  ret void\n"
    else output ++ "  ret " ++ resultType function ++ " 0\n"
  | .ret #[value] =>
    emitOperand (output ++ "  ret " ++ resultType function ++ " ") (function.results[0]?.getD .int) value ++ "\n"
  | .ret values => Id.run do
    -- Several results are packed into one struct with `insertvalue`.
    let type := resultType function
    let mut output := output
    let mut previous := "poison"
    for h : index in [:values.size] do
      let ty := function.results[index]?.getD .int
      let name := s!"%ret{blockIndex}.{index}"
      output := emitOperand (output ++ s!"  {name} = insertvalue {type} {previous}, {llvmType ty} ") ty
        values[index] ++ s!", {index}\n"
      previous := name
    return output ++ s!"  ret {type} {previous}\n"

private def emitFunction (functions : Std.HashMap String IR.Function)
    (stringIndices : Std.HashMap ByteArray Nat) (output : String)
    (function : IR.Function) : String := Id.run do
  let linkage := if Symbol.isEntry function then "" else "internal "
  let mut output := output ++ "define " ++ linkage ++ resultType function ++ " " ++ Symbol.function function.name ++ "("
  for h : index in [:function.parameters.size] do
    if index != 0 then output := output ++ ", "
    output := output ++ llvmType function.parameters[index].ty ++ " %arg" ++ toString index
  output := output ++ ") {\n"
  for h : index in [:function.blocks.size] do
    let block := function.blocks[index]
    if index != 0 then output := output ++ "\n"
    output := output ++ "bb" ++ toString index ++ ":\n"
    output := emitInstructions functions stringIndices index output block.instructions
    output := emitTerminator function index output block.terminator
  return output ++ "}\n"

def emit (program : IR.Program) : String := Id.run do
  let needs := collectRuntimeNeeds program
  -- Verified IR names every callee, so call sites can take their types from its signature.
  let functions := program.functions.foldl (fun map function => map.insert function.name function) {}
  let mut output := runtime needs
  for h : index in [:program.functions.size] do
    if index != 0 then output := output ++ "\n"
    output := emitFunction functions needs.stringIndices output program.functions[index]
  return output

end GoAot.Backend.LLVM
