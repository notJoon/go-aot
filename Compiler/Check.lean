module

public import Compiler.Checked
public import Compiler.Scope
public import Compiler.Parser.Go
import Compiler.Literal
import Std.Data.HashMap

public section

namespace GoAot.Check

private def diagnosticAt (span : Span) (message : String) : Diagnostic :=
  ⟨.lowering, some span, message⟩

private structure Signature where
  id : Checked.FunctionId
  name : String
  parameters : Array String
  returnKind : IR.ReturnKind
  -- Retain parameter bindings for lookup and duplicate declarations in the body.
  scope : Scope

private def signatures (file : Syntax.File) : Except Diagnostic (Std.HashMap String Signature) := do
  let mut result : Std.HashMap String Signature := {}
  for h : i in [:file.functions.size] do
    let function := file.functions[i]
    let name := function.name.text.copy
    unless IR.validName name do throw (diagnosticAt function.name.span s!"unsupported function name '{name}'")
    if result.contains name then
      throw (diagnosticAt function.name.span s!"duplicate function '{name}'")
    let mut parameters := #[]
    let mut scope := Scope.empty
    for parameter in function.parameters do
      if parameter.typeName.text != "int" then
        throw (diagnosticAt parameter.typeName.span s!"only int parameters are supported in function '{name}'")
      let parameterName := parameter.name.text.copy
      unless IR.validName parameterName do
        throw (diagnosticAt parameter.name.span s!"unsupported parameter name '{parameter.name.text}'")
      scope ← scope.declare parameterName
        ⟨.parameter, parameters.size, .int, parameter.name.span⟩
      parameters := parameters.push parameterName
    let returnKind ← match function.resultType with
      | none => pure .void
      | some resultType =>
        if resultType.text == "int" then pure .int
        else throw (diagnosticAt resultType.span s!"only int return values are supported in function '{name}'")
    result := result.insert name ⟨i, name, parameters, returnKind, scope⟩
  return result

private structure Context where
  all : Std.HashMap String Signature
  signature : Signature
  scope : Scope
  loopDepth : Nat := 0

private abbrev CheckM := ReaderT Context (StateT (Array IR.ValueKind) (Except Diagnostic))

@[inline] private def withScope (scope : Scope) (action : CheckM α) : CheckM α :=
  withReader (fun context => { context with scope }) action

private def checkCallable (scope : Scope) (name : String) (span : Span) : Except Diagnostic Unit := do
  if (scope.find? name).isSome then
    throw (diagnosticAt span s!"cannot call non-function '{name}'")

-- Expressions only read bindings. Keeping local allocation state out avoids a result/state pair
-- for every recursive operand check.
private partial def checkOperand :
    Syntax.Expr → ReaderT Context (Except Diagnostic) (Checked.Expr × IR.ValueKind)
  | .intLiteral text span => do
    let value := Literal.decodeInt text
    if value > IR.maxSignedInt64 then
      throw (diagnosticAt span "integer literal exceeds signed 64-bit range")
    return (.intLiteral value, .int)
  | .identifier name => do
    let some symbol := (← read).scope.find? name.text.copy
      | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
    return (.local symbol.id, symbol.valueKind)
  | .call callee arguments span => do
    let name := callee.text.copy
    if let .error error := checkCallable (← read).scope name callee.span then throw error
    let some signature := (← read).all[name]?
      | throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
    unless signature.returnKind == .int do
      throw (diagnosticAt callee.span s!"function '{callee.text}' does not return a value")
    if arguments.size != signature.parameters.size then
      throw (diagnosticAt span s!"function '{callee.text}' expects {signature.parameters.size} arguments")
    let mut checked := #[]
    for argument in arguments do
      let (value, kind) ← checkOperand argument
      unless kind == .int do throw (diagnosticAt argument.span "function arguments must be int")
      checked := checked.push value
    return (.call signature.id checked, .int)
  | .binary op left right span => do
    let (left, leftKind) ← checkOperand left
    let (right, rightKind) ← checkOperand right
    unless leftKind == .int && rightKind == .int do
      throw (diagnosticAt span "binary operands must be int")
    let (op, kind) : IR.Op × IR.ValueKind := match op with
      | .add => (.add, .int)
      | .subtract => (.subtract, .int)
      | .less => (.less, .bool)
    return (.binary op left right, kind)
  | .stringLiteral _ span => throw (diagnosticAt span "expected int expression")

private def checkPrintln (callee : Syntax.Ident) (arguments : Array Syntax.Expr)
    (span : Span) : CheckM Checked.Stmt := do
  let name := callee.text.copy
  if let .error error := checkCallable (← read).scope name callee.span then throw error
  let #[argument] := arguments
    | throw (diagnosticAt span "println expects one argument")
  match argument with
  | .stringLiteral literal span =>
    if literal.startsWith "\"" then return .printString (Literal.decodeInterpreted literal)
    else throw (diagnosticAt span "raw string literals are not supported yet")
  | _ => do
    let (value, kind) ← (checkOperand argument).run (← read)
    unless kind == .int do throw (diagnosticAt argument.span "println supports only string and int")
    return .printInt value

private def checkDeclaration (name : Syntax.Ident) (typeName : Option Syntax.Ident)
    (initializer : Option Syntax.Expr) : CheckM (Checked.Stmt × Context) := do
  if typeName.isNone && initializer.isNone then
    throw (diagnosticAt name.span "variable declaration requires a type or initializer")
  let nameText := name.text.copy
  unless IR.validName nameText && nameText != "_" do
    throw (diagnosticAt name.span s!"unsupported local name '{nameText}'")
  if let some typeName := typeName then
    unless typeName.text == "int" do
      throw (diagnosticAt typeName.span "only int variable types are supported")
  -- The initializer cannot see the binding being declared.
  let (value, kind) ← match initializer with
    | some value => (checkOperand value).run (← read)
    | none => pure (.intLiteral 0, .int)
  if typeName.isSome && kind != .int then
    throw (diagnosticAt ((initializer.map (·.span)).getD name.span) "initializer must be int")
  let id := (← get).size
  let context ← read
  let scope ← context.scope.declare nameText ⟨.local, id, kind, name.span⟩
  modify (·.push kind)
  return (.declare id value, { context with scope })

private def checkCondition (condition : Syntax.Expr) (message : String) : CheckM Checked.Expr := do
  let (value, kind) ← (checkOperand condition).run (← read)
  unless kind == .bool do throw (diagnosticAt condition.span message)
  return value

mutual
  private partial def checkStatement (statement : Syntax.Stmt) : CheckM (Checked.Stmt × Context) := do
    let context ← read
    match statement with
    | .expr (.call callee arguments span) =>
      if callee.text == "println" then
        return (← checkPrintln callee arguments span, context)
      let name := callee.text.copy
      if let .error error := checkCallable context.scope name callee.span then throw error
      let some signature := context.all[name]?
        | throw (diagnosticAt callee.span s!"unknown function '{callee.text}'")
      -- Value-returning calls share the expression path's checks; the result is dropped.
      if signature.returnKind == .int then
        let (value, _) ← (checkOperand (.call callee arguments span)).run context
        return (.discard value, context)
      if signature.name == "main" then
        throw (diagnosticAt callee.span "cannot call 'main'")
      unless arguments.size == signature.parameters.size do
        throw (diagnosticAt span s!"function '{callee.text}' expects {signature.parameters.size} arguments")
      let mut checked := #[]
      for argument in arguments do
        let (value, kind) ← (checkOperand argument).run context
        unless kind == .int do throw (diagnosticAt argument.span "function arguments must be int")
        checked := checked.push value
      return (.callVoid signature.id checked, context)
    | .varDeclaration name typeName initializer => checkDeclaration name typeName initializer
    | .assignment name value => do
      let some symbol := context.scope.find? name.text.copy
        | throw (diagnosticAt name.span s!"unknown identifier '{name.text}'")
      let (value', kind) ← (checkOperand value).run context
      unless kind == symbol.valueKind do
        throw (diagnosticAt value.span "assignment type does not match variable type")
      return (.assign symbol.id value', context)
    | .expr value => throw (diagnosticAt value.span "only function calls may be used as statements")
    | .return value span => do
      let signature := context.signature
      match signature.returnKind, value with
      | .void, none => return (.return none, context)
      | .void, some value =>
        throw (diagnosticAt value.span s!"function '{signature.name}' returns no value")
      | .int, none =>
        throw (diagnosticAt span s!"function '{signature.name}' must return a value")
      | .int, some value =>
        let (value', kind) ← (checkOperand value).run context
        unless kind == .int do throw (diagnosticAt value.span "return value must be int")
        return (.return (some value'), context)
    | .break span => do
      if context.loopDepth == 0 then throw (diagnosticAt span "break outside loop")
      return (.break, context)
    | .continue span => do
      if context.loopDepth == 0 then throw (diagnosticAt span "continue outside loop")
      return (.continue, context)
    | .ifThen condition body elseBody => do
      let value ← checkCondition condition "if condition must be bool"
      let yes ← withScope context.scope.enter (checkStatements body)
      let no ← elseBody.mapM fun statements => withScope context.scope.enter (checkStatements statements)
      return (.ifThen value yes no, context)
    | .forLoop initializer condition post body => do
      let loopScope := context.scope.enter
      let (init, loopContext) ← match initializer with
        | some statement => do
          let (checked, next) ← withScope loopScope (checkStatement statement)
          pure (some checked, next)
        | none => pure (none, { context with scope := loopScope })
      let loopScope := loopContext.scope
      let test ← condition.mapM fun condition =>
        withScope loopScope (checkCondition condition "for condition must be bool")
      let bodyContext := { loopContext with scope := loopScope.enter, loopDepth := context.loopDepth + 1 }
      let body' ← withReader (fun _ => bodyContext) (checkStatements body)
      let post' ← post.mapM fun statement => do
        let (checked, _) ← withScope loopScope (checkStatement statement)
        return checked
      return (.forLoop init test post' body', context)

  private partial def checkStatements (statements : Array Syntax.Stmt) : CheckM (Array Checked.Stmt) := do
    let mut context ← read
    let mut checked := #[]
    for statement in statements do
      let (next, nextContext) ← withReader (fun _ => context) (checkStatement statement)
      checked := checked.push next
      context := nextContext
    return checked
end

private partial def hasOwnBreak (statements : Array Syntax.Stmt) : Bool :=
  statements.any fun statement =>
    match statement with
    | .break _ => true
    | .ifThen _ yes elseBody =>
      hasOwnBreak yes || (elseBody.map hasOwnBreak).getD false
    -- A nested loop consumes its own break.
    | .forLoop .. => false
    | .varDeclaration .. | .assignment .. | .expr _ | .return .. | .continue _ => false

-- Return rules describe source syntax, even when CFG edges later make a path unreachable.
private partial def isTerminating (statements : Array Syntax.Stmt) : Bool :=
  match statements.back? with
  | some (.return ..) => true
  | some (.ifThen _ yes (some no)) => isTerminating yes && isTerminating no
  | some (.forLoop _ none _ body) => !hasOwnBreak body
  | _ => false

/-- Check the whole source, including unreachable statements, and resolve names to stable IDs.
User diagnostics retain the public `lowering` phase. -/
def check (file : Syntax.File) : Except Diagnostic Checked.File := do
  if file.packageName.text != "main" then throw (diagnosticAt file.packageName.span "expected package main")
  -- Collect every signature before checking bodies to allow forward calls and recursion.
  let all ← signatures file
  let some main := all["main"]? | throw ⟨.lowering, none, "expected main function"⟩
  unless main.parameters.isEmpty && main.returnKind == .void do
    throw ⟨.lowering, (file.functions.find? (·.name.text == "main".toSlice)).map (·.span),
      "main must have no parameters or return value"⟩
  let mut functions := #[]
  for function in file.functions do
    let some signature := all[function.name.text.copy]?
      | throw (diagnosticAt function.name.span "internal error: missing function signature")
    let initial := Array.replicate signature.parameters.size IR.ValueKind.int
    let (body, locals) ← ((checkStatements function.body).run
      ⟨all, signature, signature.scope, 0⟩).run initial
    if signature.returnKind == .int && !isTerminating function.body then
      throw (diagnosticAt function.span s!"function '{signature.name}' must end with return")
    functions := functions.push ⟨signature.name, signature.parameters, locals,
      signature.returnKind, body⟩
  return ⟨functions⟩

end GoAot.Check
