module

public import Compiler.IR
public import Compiler.Parser.Go

public section

namespace GoAot.Lowering

private def diagnosticAt (span : Span) (message : String) : Diagnostic :=
  ⟨.lowering, some span, message⟩

private inductive Scalar where
  | int (value : IR.IntExpr)
  | bool (value : IR.BoolExpr)

private structure Signature where
  name : String
  parameters : Array String
  returnsInt : Bool

private def signatures (file : Syntax.File) : Except Diagnostic (Array Signature) := do
  let mut result := #[]
  for function in file.functions do
    let name := function.name.text
    unless IR.validName name do throw (diagnosticAt function.name.span s!"unsupported function name '{name}'")
    if result.any (fun (signature : Signature) => signature.name == name) then
      throw (diagnosticAt function.name.span s!"duplicate function '{name}'")
    let mut parameters := #[]
    for parameter in function.parameters do
      if parameter.typeName.text != "int" then
        throw (diagnosticAt parameter.typeName.span s!"only int parameters are supported in function '{name}'")
      unless IR.validName parameter.name.text do
        throw (diagnosticAt parameter.name.span s!"unsupported parameter name '{parameter.name.text}'")
      if parameters.contains parameter.name.text then
        throw (diagnosticAt parameter.name.span s!"duplicate parameter '{parameter.name.text}'")
      parameters := parameters.push parameter.name.text
    let returnsInt ← match function.resultType with
      | none => pure false
      | some resultType =>
        if resultType.text == "int" then pure true
        else throw (diagnosticAt resultType.span s!"only int return values are supported in function '{name}'")
    result := result.push ⟨name, parameters, returnsInt⟩
  return result

private def findSignature? (all : Array Signature) (name : String) : Option Signature :=
  all.find? fun signature => signature.name == name

private def digitValue (radix : Nat) (c : Char) : Option Nat :=
  let value :=
    if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
    else if 'a' <= c && c <= 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' <= c && c <= 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  value.filter (· < radix)

private def takeDigits (span : Span) (radix : Nat) : Nat → List Char → Except Diagnostic (Nat × List Char)
  | 0, rest => return (0, rest)
  | count + 1, c :: rest => do
    let some digit := digitValue radix c | throw (diagnosticAt span "invalid string escape")
    let (tail, rest) ← takeDigits span radix count rest
    return (digit * radix ^ count + tail, rest)
  | _, [] => throw (diagnosticAt span "incomplete string escape")

private def pushChar (bytes : ByteArray) (c : Char) : ByteArray := Id.run do
  let mut result := bytes
  for byte in (String.singleton c).toUTF8 do result := result.push byte
  return result

-- Decode source escapes once at the semantic boundary so backends never reinterpret Go syntax.
private partial def decodeStringChars (span : Span) (chars : List Char) (bytes : ByteArray) :
    Except Diagnostic ByteArray := do
  match chars with
  | [] => return bytes
  | '\\' :: escaped :: rest =>
    let simple? := match escaped with
      | 'a' => some 7 | 'b' => some 8 | 'f' => some 12 | 'n' => some 10
      | 'r' => some 13 | 't' => some 9 | 'v' => some 11
      | '\\' => some 92 | '"' => some 34
      | _ => none
    if let some byte := simple? then
      decodeStringChars span rest (bytes.push byte.toUInt8)
    else if escaped == 'x' then
      let (value, rest) ← takeDigits span 16 2 rest
      decodeStringChars span rest (bytes.push value.toUInt8)
    else if escaped == 'u' || escaped == 'U' then
      let (value, rest) ← takeDigits span 16 (if escaped == 'u' then 4 else 8) rest
      decodeStringChars span rest (pushChar bytes (Char.ofNat value))
    else if '0' <= escaped && escaped <= '7' then
      let (tail, rest) ← takeDigits span 8 2 rest
      decodeStringChars span rest (bytes.push ((escaped.toNat - '0'.toNat) * 64 + tail).toUInt8)
    else
      throw (diagnosticAt span "invalid string escape")
  | '\\' :: [] => throw (diagnosticAt span "incomplete string escape")
  | c :: rest => decodeStringChars span rest (pushChar bytes c)

private def decodeString (literal : String) (span : Span) : Except Diagnostic ByteArray := do
  match literal.toList with
  | '"' :: rest =>
    match rest.reverse with
    | '"' :: reversed => decodeStringChars span reversed.reverse ByteArray.empty
    | _ => throw (diagnosticAt span "unterminated string literal")
  | _ => throw (diagnosticAt span "raw string literals are not supported yet")

private partial def lowerScalar (all : Array Signature) (locals : Array String) :
    Syntax.Expr → Except Diagnostic Scalar
  | .intLiteral text span =>
    match text.toNat? with
    | some value => do
      if value > 9223372036854775807 then
        throw (diagnosticAt span "integer literal exceeds signed 64-bit range")
      return .int (.literal value)
    | none => throw (diagnosticAt span s!"unsupported integer literal '{text}'")
  | .identifier name => do
    let some index := locals.findIdx? (· == name.text)
      | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
    return .int (.argument index)
  | .call callee arguments span => do
    let some signature := findSignature? all callee.text
      | throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
    unless signature.returnsInt do
      throw (diagnosticAt callee.span s!"function '{callee.text}' does not return a value")
    if arguments.size != signature.parameters.size then
      throw (diagnosticAt span s!"function '{callee.text}' expects {signature.parameters.size} arguments")
    let mut lowered := #[]
    for argument in arguments do
      let .int value ← lowerScalar all locals argument
        | throw (diagnosticAt argument.span "function arguments must be int")
      lowered := lowered.push value
    return .int (.call callee.text lowered)
  | .binary op left right span => do
    let left ← lowerScalar all locals left
    let right ← lowerScalar all locals right
    let (.int left, .int right) := (left, right)
      | throw (diagnosticAt span "binary operands must be int")
    match op with
    | .add => return .int (.add left right)
    | .subtract => return .int (.subtract left right)
    | .less => return .bool (.less left right)
  | .stringLiteral _ span => throw (diagnosticAt span "expected int expression")

private structure PendingBlock where
  instructions : Array IR.Instruction := #[]
  terminator : Option IR.Terminator := none

private structure Builder where
  blocks : Array PendingBlock := #[{}]
  current : Option IR.BlockId := some 0

private def builderError : Diagnostic :=
  ⟨.lowering, none, "internal error: invalid CFG builder state"⟩

private def Builder.newBlock (builder : Builder) : IR.BlockId × Builder :=
  (builder.blocks.size, { builder with blocks := builder.blocks.push {} })

private def Builder.emit (builder : Builder) (instruction : IR.Instruction) :
    Except Diagnostic Builder := do
  let some current := builder.current | throw builderError
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  let blocks := builder.blocks.set! current { block with instructions := block.instructions.push instruction }
  return { builder with blocks }

private def Builder.terminate (builder : Builder) (terminator : IR.Terminator) :
    Except Diagnostic Builder := do
  let some current := builder.current | throw builderError
  let some block := builder.blocks[current]? | throw builderError
  if block.terminator.isSome then throw builderError
  return { blocks := builder.blocks.set! current ({ block with terminator := some terminator })
           current := none }

private def Builder.selectBlock (builder : Builder) (target : IR.BlockId) :
    Except Diagnostic Builder := do
  let some block := builder.blocks[target]? | throw builderError
  if builder.current.isSome || block.terminator.isSome then throw builderError
  return { builder with current := some target }

private def Builder.finish (builder : Builder) : Except Diagnostic (Array IR.Block) := do
  if builder.current.isSome then throw builderError
  builder.blocks.mapM fun block => do
    let some terminator := block.terminator | throw builderError
    return ⟨block.instructions, terminator⟩

mutual
  private partial def lowerStatement (all : Array Signature) (signature : Signature)
      (builder : Builder) : Syntax.Stmt → Except Diagnostic Builder
    | .expr (.call callee arguments span) => do
      if callee.text != "println" then
        throw (diagnosticAt callee.span "only println calls may be used as statements")
      let some argument := arguments[0]?
        | throw (diagnosticAt span "println expects one argument")
      if arguments.size != 1 then throw (diagnosticAt span "println expects one argument")
      let instruction ← match argument with
        | .stringLiteral literal span =>
          pure (IR.Instruction.printString (← decodeString literal span))
        | _ => do
          let .int value ← lowerScalar all signature.parameters argument
            | throw (diagnosticAt argument.span "println supports only string and int")
          pure (.printInt value)
      if builder.current.isSome then builder.emit instruction else pure builder
    | .expr value => throw (diagnosticAt value.span "only function calls may be used as statements")
    | .return value => do
      unless signature.returnsInt do throw (diagnosticAt value.span s!"function '{signature.name}' returns no value")
      let .int value ← lowerScalar all signature.parameters value
        | throw (diagnosticAt value.span "return value must be int")
      if builder.current.isSome then builder.terminate (.ret (some value)) else pure builder
    | .ifThen condition body => do
      let .bool condition ← lowerScalar all signature.parameters condition
        | throw (diagnosticAt condition.span "if condition must be bool")
      -- Closed paths still check source semantics, without reserving unreachable blocks.
      if builder.current.isNone then return ← lowerStatements all signature builder body
      let (thenBlock, builder) := builder.newBlock
      let (continuation, builder) := builder.newBlock
      let builder ← builder.terminate (.condBr condition thenBlock continuation)
      let builder ← builder.selectBlock thenBlock
      let builder ← lowerStatements all signature builder body
      let builder ← if builder.current.isSome then builder.terminate (.br continuation) else pure builder
      builder.selectBlock continuation

  private partial def lowerStatements (all : Array Signature) (signature : Signature)
      (builder : Builder) (statements : Array Syntax.Stmt) : Except Diagnostic Builder := do
    let mut builder := builder
    for statement in statements do
      builder ← lowerStatement all signature builder statement
    return builder
end

def lower (file : Syntax.File) : Except Diagnostic IR.Program := do
  if file.packageName.text != "main" then throw (diagnosticAt file.packageName.span "expected package main")
  let all ← signatures file
  let some main := findSignature? all "main" | throw ⟨.lowering, none, "expected main function"⟩
  unless main.parameters.isEmpty && !main.returnsInt do
    throw ⟨.lowering, (file.functions.find? (·.name.text == "main")).map (·.span),
      "main must have no parameters or return value"⟩
  let mut functions := #[]
  for function in file.functions do
    let some signature := findSignature? all function.name.text
      | throw (diagnosticAt function.name.span "internal error: missing function signature")
    if signature.name != "main" && !signature.returnsInt then
      throw (diagnosticAt function.name.span s!"function '{signature.name}' must return int")
    let builder ← lowerStatements all signature {} function.body
    if signature.returnsInt then
      match function.body[function.body.size - 1]? with
      | some (.return _) => pure ()
      | _ => throw (diagnosticAt function.span s!"function '{signature.name}' must end with return")
    let builder ← if builder.current.isSome then
        if signature.returnsInt then throw builderError else builder.terminate (.ret none)
      else pure builder
    let blocks ← builder.finish
    functions := functions.push ⟨signature.name, signature.parameters,
      if signature.returnsInt then .int else .void, blocks⟩
  return ⟨functions⟩

end GoAot.Lowering
