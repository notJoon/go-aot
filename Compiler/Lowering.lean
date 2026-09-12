module

public import Compiler.IR
public import Compiler.Parser.Go

public section

namespace GoAot.Lowering

private inductive Scalar where
  | int (value : IR.IntExpr)
  | bool (value : IR.BoolExpr)

private structure Signature where
  name : String
  parameters : Array String
  returnsInt : Bool

private def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def validName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => (asciiLetter first || first == '_') &&
      rest.all fun c => asciiLetter c || asciiDigit c || c == '_'

private def signatures (file : Syntax.File) : Except String (Array Signature) := do
  let mut result := #[]
  for function in file.functions do
    let name := function.name.text
    unless validName name do throw s!"unsupported function name '{name}'"
    if result.any (fun (signature : Signature) => signature.name == name) then
      throw s!"duplicate function '{name}'"
    let mut parameters := #[]
    for parameter in function.parameters do
      if parameter.typeName.text != "int" then
        throw s!"only int parameters are supported in function '{name}'"
      unless validName parameter.name.text do
        throw s!"unsupported parameter name '{parameter.name.text}'"
      if parameters.contains parameter.name.text then
        throw s!"duplicate parameter '{parameter.name.text}'"
      parameters := parameters.push parameter.name.text
    let returnsInt ← match function.resultType with
      | none => pure false
      | some resultType =>
        if resultType.text == "int" then pure true
        else throw s!"only int return values are supported in function '{name}'"
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

private def takeDigits (radix : Nat) : Nat → List Char → Except String (Nat × List Char)
  | 0, rest => return (0, rest)
  | count + 1, c :: rest => do
    let some digit := digitValue radix c | throw "invalid string escape"
    let (tail, rest) ← takeDigits radix count rest
    return (digit * radix ^ count + tail, rest)
  | _, [] => throw "incomplete string escape"

private def pushChar (bytes : ByteArray) (c : Char) : ByteArray := Id.run do
  let mut result := bytes
  for byte in (String.singleton c).toUTF8 do result := result.push byte
  return result

-- Decode source escapes once at the semantic boundary so backends never reinterpret Go syntax.
private partial def decodeStringChars (chars : List Char) (bytes : ByteArray) :
    Except String ByteArray := do
  match chars with
  | [] => return bytes
  | '\\' :: escaped :: rest =>
    let simple? := match escaped with
      | 'a' => some 7 | 'b' => some 8 | 'f' => some 12 | 'n' => some 10
      | 'r' => some 13 | 't' => some 9 | 'v' => some 11
      | '\\' => some 92 | '"' => some 34
      | _ => none
    if let some byte := simple? then
      decodeStringChars rest (bytes.push byte.toUInt8)
    else if escaped == 'x' then
      let (value, rest) ← takeDigits 16 2 rest
      decodeStringChars rest (bytes.push value.toUInt8)
    else if escaped == 'u' || escaped == 'U' then
      let (value, rest) ← takeDigits 16 (if escaped == 'u' then 4 else 8) rest
      decodeStringChars rest (pushChar bytes (Char.ofNat value))
    else if '0' <= escaped && escaped <= '7' then
      let (tail, rest) ← takeDigits 8 2 rest
      decodeStringChars rest (bytes.push ((escaped.toNat - '0'.toNat) * 64 + tail).toUInt8)
    else
      throw "invalid string escape"
  | '\\' :: [] => throw "incomplete string escape"
  | c :: rest => decodeStringChars rest (pushChar bytes c)

private def decodeString (literal : String) : Except String ByteArray := do
  match literal.toList with
  | '"' :: rest =>
    match rest.reverse with
    | '"' :: reversed => decodeStringChars reversed.reverse ByteArray.empty
    | _ => throw "unterminated string literal"
  | _ => throw "raw string literals are not supported yet"

private partial def lowerScalar (all : Array Signature) (locals : Array String) :
    Syntax.Expr → Except String Scalar
  | .intLiteral text _ =>
    match text.toNat? with
    | some value => do
      if value > 9223372036854775807 then
        throw "integer literal exceeds signed 64-bit range"
      return .int (.literal value)
    | none => throw s!"unsupported integer literal '{text}'"
  | .identifier name => do
    let some index := locals.findIdx? (· == name.text)
      | throw s!"unknown identifier '{name.text}'"
    return .int (.argument index)
  | .call callee arguments _ => do
    let some signature := findSignature? all callee.text
      | throw s!"unknown function '{callee.text}'"
    unless signature.returnsInt do
      throw s!"function '{callee.text}' does not return a value"
    if arguments.size != signature.parameters.size then
      throw s!"function '{callee.text}' expects {signature.parameters.size} arguments"
    let mut lowered := #[]
    for argument in arguments do
      let .int value ← lowerScalar all locals argument
        | throw "function arguments must be int"
      lowered := lowered.push value
    return .int (.call callee.text lowered)
  | .binary op left right _ => do
    let left ← lowerScalar all locals left
    let right ← lowerScalar all locals right
    let (.int left, .int right) := (left, right)
      | throw "binary operands must be int"
    match op with
    | .add => return .int (.add left right)
    | .subtract => return .int (.subtract left right)
    | .less => return .bool (.less left right)
  | .stringLiteral _ _ => throw "expected int expression"

mutual
  private partial def lowerStatement (all : Array Signature) (signature : Signature) :
      Syntax.Stmt → Except String IR.Instruction
    | .expr (.call callee arguments _) => do
      if callee.text != "println" then
        throw "only println calls may be used as statements"
      let some argument := arguments[0]?
        | throw "println expects one argument"
      if arguments.size != 1 then throw "println expects one argument"
      match argument with
      | .stringLiteral literal _ =>
        return .printString (← decodeString literal)
      | _ =>
        let .int value ← lowerScalar all signature.parameters argument
          | throw "println supports only string and int"
        return .printInt value
    | .expr _ => throw "only function calls may be used as statements"
    | .return value => do
      unless signature.returnsInt do throw s!"function '{signature.name}' returns no value"
      let .int value ← lowerScalar all signature.parameters value
        | throw "return value must be int"
      return .return value
    | .ifThen condition body => do
      let .bool condition ← lowerScalar all signature.parameters condition
        | throw "if condition must be bool"
      return .ifThen condition (← lowerStatements all signature body)

  private partial def lowerStatements (all : Array Signature) (signature : Signature)
      (statements : Array Syntax.Stmt) : Except String (Array IR.Instruction) := do
    let mut result := #[]
    for statement in statements do
      result := result.push (← lowerStatement all signature statement)
    return result
end

def lower (file : Syntax.File) : Except String IR.Program := do
  if file.packageName.text != "main" then throw "expected package main"
  let all ← signatures file
  let some main := findSignature? all "main" | throw "expected main function"
  unless main.parameters.isEmpty && !main.returnsInt do
    throw "main must have no parameters or return value"
  let mut functions := #[]
  for function in file.functions do
    let some signature := findSignature? all function.name.text
      | throw "internal error: missing function signature"
    if signature.name != "main" && !signature.returnsInt then
      throw s!"function '{signature.name}' must return int"
    let body ← lowerStatements all signature function.body
    if signature.returnsInt then
      match body[body.size - 1]? with
      | some (.return _) => pure ()
      | _ => throw s!"function '{signature.name}' must end with return"
    functions := functions.push ⟨signature.name, signature.parameters, body⟩
  return ⟨functions⟩

end GoAot.Lowering
