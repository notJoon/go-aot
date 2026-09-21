import Compiler.Check

open GoAot

private def checked (text : String) : Option Checked.File :=
  (parse (Source.ofString text) >>= Check.check).toOption

#guard match checked
    "package main\nfunc f(x int) int { y := x; if x < 1 { x := y; return x }; return y }\nfunc main() { println(f(1)) }" with
  | some file => match file.functions[0]? with
    | some function => function.name == "f" && function.locals == #[.int, .int, .int] &&
      match function.body with
      | #[Checked.Stmt.declare 1 (.local 0),
          .ifThen (.binary .less (.local 0) (.intLiteral 1))
            #[.declare 2 (.local 1), .return (some (.local 2))] none,
          .return (some (.local 1))] => true
      | _ => false
    | none => false
  | none => false

#guard match checked
    "package main\nfunc f(x int) int { return g(x) }\nfunc g(x int) int { return f(x) }\nfunc main() {}" with
  | some file => match file.functions[0]?.map (·.body), file.functions[1]?.map (·.body) with
    | some #[Checked.Stmt.return (some (.call 1 #[.local 0]))],
      some #[Checked.Stmt.return (some (.call 0 #[.local 0]))] => true
    | _, _ => false
  | none => false

#guard [
    ("func f() int { return 1; println(missing) }; func main() {}", "unknown identifier 'missing'"),
    ("func f() int { return 1; for { break; println(1 < 2) } }; func main() {}",
      "println supports only string and int"),
    ("func main() { x := x }", "unknown identifier 'x'")].all fun (body, message) =>
  match parse (Source.ofString ("package main\n" ++ body)) >>= Check.check with
  | .error error => error.phase == .lowering && error.message == message
  | .ok _ => false

#guard match checked "package main\nfunc main() { var x int; x = 1 }" with
  | some file => match file.functions[0]?.map (·.body) with
    | some #[Checked.Stmt.declare 0 (.intLiteral 0), .assign 0 (.intLiteral 1)] => true
    | _ => false
  | none => false
