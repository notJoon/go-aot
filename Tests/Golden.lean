import GoAot
import Compiler.Parser.Go
import Compiler.IR.Verify
import Compiler.Backend.LLVM

open GoAot

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def renderFile (file : Syntax.File) : String := Id.run do
  let packageName := file.packageName
  let mut output := s!"package {packageName.text} {packageName.span.start}:{packageName.span.stop}\n"
  for function in file.functions do
    let name := function.name
    output := output ++ s!"func {name.text} {name.span.start}:{name.span.stop} " ++
      s!"{function.span.start}:{function.span.stop}\n"
  return output

private def renderParse (text : String) : String :=
  match parse (Source.ofString text) with
  | .ok file => renderFile file
  | .error diagnostic => "error " ++ diagnostic.render (Source.ofString text) ++ "\n"

private def checkGolden (name : String) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let input ← IO.FS.readFile (path ++ ".go")
  let expected ← IO.FS.readFile (path ++ ".golden")
  let actual := renderParse input
  check (actual == expected) s!"golden mismatch: {name}\nexpected:\n{expected}actual:\n{actual}"

-- The Lean toolchain Clang on macOS cannot locate the host SDK during linking.
private def clangCommand : IO String :=
  return (← IO.getEnv "CLANG").getD (if System.Platform.isOSX then "/usr/bin/clang" else "clang")

-- Verify input SSA and every transformed module before code generation.
private def llvmOptions : Array String :=
  #["-Wno-override-module", "-Xclang", "-llvm-verify-each"]

/-- IR that relies on poison or undefined behavior often works at only one of these levels. -/
private def optimizationLevels : List String := ["-O0", "-O2"]

private def runLLVM (generated : String) (level : String := "-O2") : IO IO.Process.Output :=
  IO.FS.withTempDir fun dir => do
    let sourcePath := dir / "program.ll"
    let exePath := dir / "program"
    IO.FS.writeFile sourcePath generated
    let args := #[level] ++ llvmOptions ++ #["-x", "ir", sourcePath.toString, "-o", exePath.toString]
    let result ← IO.Process.output { cmd := ← clangCommand, args }
    unless result.exitCode == 0 do throw (IO.userError result.stderr)
    IO.Process.output { cmd := exePath.toString }

private def compileOrThrow (name : String) (source : Source) : IO String :=
  match compileToLLVM source with
  | .ok generated => pure generated
  | .error diagnostic => throw (IO.userError s!"compile failed: {name}: {diagnostic.render source}")

/-- Run a golden program and compare its output, and its LLVM IR when an `.ll.golden` exists. -/
private def checkProgram (name : String) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let source := Source.ofString (← IO.FS.readFile (path ++ ".go"))
  let expected ← IO.FS.readFile (path ++ ".out.golden")
  let generated ← compileOrThrow name source
  if ← System.FilePath.pathExists (path ++ ".ll.golden") then
    let golden ← IO.FS.readFile (path ++ ".ll.golden")
    check (generated == golden) s!"LLVM golden mismatch: {name}\n{generated}"
  for level in optimizationLevels do
    let output ← runLLVM generated level
    check (output.exitCode == 0 && output.stdout == expected)
      s!"wrong output at {level}: {name}: {repr output.stdout}"
  if name == "hello" || name == "locals" then
    IO.FS.withTempDir fun dir => do
      let llvmPath := dir / "program.ll"
      let optimizedPath := dir / "optimized.ll"
      IO.FS.writeFile llvmPath generated
      let optimizeArgs := #["-O2"] ++ llvmOptions ++ #["-S", "-emit-llvm", "-x", "ir", llvmPath.toString,
        "-o", optimizedPath.toString]
      discard <| IO.Process.run { cmd := ← clangCommand, args := optimizeArgs }
      let optimized ← IO.FS.readFile optimizedPath
      check (optimized.contains "target datalayout") "optimized LLVM IR has no data layout"
      check (optimized.contains "target triple") "optimized LLVM IR has no target triple"
      if name == "locals" then
        check (!optimized.contains "alloca ") "optimized locals still contain stack allocations"

/--
The expected outputs are gc's: `go run` must print each `.out.golden` exactly. Go's `println`
writes to stderr. Go 1.26 is the first version checked to print floats in the shortest form the
goldens use, so the check is skipped when `go`, or the command in `GO`, is missing or older.
-/
private def checkGoOracle (names : Array String) : IO Unit := do
  let go := (← IO.getEnv "GO").getD "go"
  let version ← try
      let output ← IO.Process.output { cmd := go, args := #["env", "GOVERSION"] }
      pure (if output.exitCode == 0 then output.stdout.trimAscii.copy else "")
    catch _ => pure ""
  -- `go1.26.2` and `go1.26rc1` both have minor version 26.
  let minor := match (version.dropPrefix "go1.").copy.splitOn "." with
    | minor :: _ => (minor.takeWhile Char.isDigit).copy.toNat?
    | [] => none
  unless version.startsWith "go1." && minor.any (· ≥ 26) do
    IO.println s!"Go oracle skipped: needs go1.26 or later, found '{version}'"
    return
  -- Out of range float conversions are implementation defined in Go, and this compiler follows
  -- gc on arm64, so gc on another architecture prints something else for this program (#60).
  let arm64 := System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64"
  let names := if arm64 then names else names.filter (· != "float_conversion")
  -- Each `go run` mostly waits on the Go toolchain, so they run concurrently.
  let runs ← names.mapM fun name =>
    IO.asTask (IO.Process.output { cmd := go, args := #["run", "Tests/Golden/" ++ name ++ ".go"] })
  for name in names, run in runs do
    let output ← IO.ofExcept (← IO.wait run)
    let expected ← IO.FS.readFile ("Tests/Golden/" ++ name ++ ".out.golden")
    check (output.exitCode == 0 && output.stderr == expected)
      s!"gc disagrees with {name}.out.golden: {repr output.stderr}"
  IO.println s!"Go oracle: {names.size} programs match gc"

private def checkDeadControlFlow (name : String) : IO Unit := do
  let source := Source.ofString (← IO.FS.readFile ("Tests/Golden/" ++ name ++ ".go"))
  let generated ← compileOrThrow name source
  check (!generated.contains "dead marker") s!"unreachable code was emitted: {name}"

-- Byte comparison makes embedded NUL truncation observable.
private def checkNulString : IO Unit := do
  let source := Source.ofString (← IO.FS.readFile "Tests/Golden/nul.go")
  let output ← runLLVM (← compileOrThrow "nul" source)
  check (output.exitCode == 0 && output.stdout.toUTF8 == ByteArray.mk #[97, 0, 98, 10])
    "LLVM changed NUL bytes"

private def checkInvalidSSARejected : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let llvmPath := dir / "invalid.ll"
    let objectPath := dir / "invalid.o"
    IO.FS.writeFile llvmPath (← IO.FS.readFile "Tests/Golden/invalid_ssa.ll")
    let result ← IO.Process.output {
      cmd := ← clangCommand
      args := #["-O2"] ++ llvmOptions ++ #["-x", "ir", "-c", llvmPath.toString, "-o", objectPath.toString]
    }
    check (result.exitCode != 0) "LLVM verifier accepted invalid SSA"

-- Go prints this line first, followed by a goroutine trace this runtime does not have.
private def checkPanics : IO Unit := do
  let divide := "panic: runtime error: integer divide by zero\n"
  for (body, message) in [("z := 0; println(1 / z)", divide), ("z := 0; println(1 % z)", divide),
      ("var z uint64; println(1 / z)", divide), ("var z uint8; println(1 % z)", divide),
      ("s := -1; println(1 << s)", "panic: runtime error: negative shift amount\n"),
      ("var s int8 = -1; println(uint8(1) >> s)", "panic: runtime error: negative shift amount\n")] do
    let source := Source.ofString s!"package main\nfunc main() \{ println(1); {body} }\n"
    let generated ← compileOrThrow body source
    for level in optimizationLevels do
      let output ← runLLVM generated level
      check (output.exitCode == 2 && output.stdout == "1\n" && output.stderr == message)
        s!"wrong panic at {level} for {body}: {repr output.stdout} {repr output.stderr}"

private def checkDirectCFG : IO Unit := do
  let program : IR.Program := ⟨#[
    ⟨"main", #[], #[], #[⟨#[.call #[0] "walk" #[], .print .int (.value 0)], .ret #[]⟩]⟩,
    ⟨"walk", #[], #[.int], #[
      ⟨#[], .br 2⟩,
      ⟨#[.print .int (.literal 11)], .ret #[(.literal 7)]⟩,
      ⟨#[.binary 0 .less .int (.literal 1) (.literal 0)], .condBr (.value 0) 2 1⟩,
      ⟨#[], .br 3⟩]⟩]⟩
  let .ok () := IR.verify program | throw (IO.userError "valid cyclic CFG rejected")
  let output ← runLLVM (Backend.LLVM.emit program)
  check (output.exitCode == 0 && output.stdout == "11\n7\n")
    "direct CFG did not follow backward/conditional edges"
  let output ← runLLVM (← compileOrThrow "empty main" (Source.ofString "package main\nfunc main() {}\n"))
  check (output.exitCode == 0 && output.stdout.isEmpty) "empty main did not return successfully"

def goldenMain : IO Unit := do
  let entries ← ("Tests/Golden" : System.FilePath).readDir
  let mut programs := #[]
  for file in (entries.map (·.fileName)).qsort (· < ·) do
    if file.endsWith ".ll.golden" then
      pure ()
    else if file.endsWith ".out.golden" then
      programs := programs.push (file.dropSuffix ".out.golden").copy
    else if file.endsWith ".golden" then
      checkGolden (file.dropSuffix ".golden").copy
  -- Programs mostly wait on Clang and are independent, so they compile and run concurrently.
  let runs ← programs.mapM fun name => IO.asTask (checkProgram name)
  for run in runs do IO.ofExcept (← IO.wait run)
  checkDeadControlFlow "for_dead_control"
  checkDeadControlFlow "for_dead_after_loop"
  checkDeadControlFlow "for_dead_post"
  checkDirectCFG
  checkNulString
  checkInvalidSSARejected
  checkPanics
  checkGoOracle programs
  for (source, expected) in [
      ("package main\nfunc main() { println(missing()) }\n", "2:23: unknown function 'missing'"),
      ("package main\nfunc f(n int) int { return n }\nfunc main() { println(f()) }\n",
        "3:23: function 'f' expects 1 arguments"),
      ("package main\nfunc main() { println(9223372036854775808) }\n",
        "2:23: constant 9223372036854775808 overflows int"),
      ("package main\nfunc f() {}\nfunc main() { println(f()) }\n",
        "3:23: function 'f' does not return a value"),
      ("package main\nfunc main() { 1 }\n", "2:15: only function calls may be used as statements"),
      ("package main\nfunc f(n int) int { return n }\nfunc main() { f(1) + 1 }\n",
        "3:15: only function calls may be used as statements"),
      ("package main\nfunc f(n int) int { return n }\nfunc main() { f() }\n",
        "3:15: function 'f' expects 1 arguments"),
      ("package main\nfunc f(n int) int { return n }\nfunc main() { f(1 < 2) }\n",
        "3:17: function arguments must be int"),
      ("package main\nfunc main() { missing() }\n", "2:15: unknown function 'missing'"),
      ("package main\nfunc main() { println(1 + true) }\n", "2:27: operator + is not defined on bool"),
      ("package main\nfunc main() { println(1 / 0) }\n", "2:27: division by zero"),
      ("package main\nfunc main() { println(1 % 0x0) }\n", "2:27: division by zero"),
      ("package main\nfunc main() { println(1 == true) }\n",
        "2:28: mismatched types untyped int and bool"),
      ("package main\nfunc main() { if 1 && true {} }\n", "2:18: logical operands must be bool"),
      ("package main\nfunc main() { if true || 1 {} }\n", "2:26: logical operands must be bool"),
      ("package main\nfunc main() { println(-true) }\n", "2:24: operator - is not defined on bool"),
      ("package main\nfunc main() { if !1 {} }\n", "2:19: operator ! is not defined on untyped int"),
      ("package main\nfunc main() { println(true < false) }\n", "2:23: operator < is not defined on bool"),
      ("package main\nfunc main() { println(true + 1) }\n", "2:23: operator + is not defined on bool"),
      ("package main\nfunc f(b bool) bool { return b }\nfunc main() { f(1) }\n",
        "3:17: function arguments must be bool"),
      ("package main\nfunc f() bool { return 1 }\nfunc main() {}\n", "2:24: return value must be bool"),
      ("package main\nfunc main() { var b bool = 1 }\n", "2:28: initializer must be bool"),
      ("package main\nfunc main() { b := true; b = 1 }\n",
        "2:30: assignment type does not match variable type"),
      ("package main\nfunc main() { main() }\n", "2:15: cannot call 'main'"),
      ("package main\nfunc main() { println(1 << 70) }\n", "2:23: constant 1180591620717411303424 overflows int"),
      ("package main\nfunc main() { var x int8 = 200 }\n", "2:28: constant 200 overflows int8"),
      ("package main\nfunc main() { var x uint8 = -1 }\n", "2:29: constant -1 overflows uint8"),
      ("package main\nfunc main() { var x int = 2.5 }\n", "2:27: constant 2.5 truncated to int"),
      ("package main\nfunc main() { println(1e400) }\n", "2:23: constant overflows float64"),
      ("package main\nfunc main() { var a int8; var b int16; println(a + b) }\n",
        "2:52: mismatched types int8 and int16"),
      ("package main\nfunc main() { println(1.5 % 2) }\n", "2:23: operator % is not defined on untyped float"),
      ("package main\nfunc main() { f := 1.5; println(f & 1) }\n", "2:33: operator & is not defined on float64"),
      ("package main\nfunc main() { f := 1.5; println(f << 1) }\n",
        "2:33: operator << is not defined on float64"),
      ("package main\nfunc main() { println(1 << -1) }\n", "2:28: negative shift count"),
      ("package main\nfunc main() { println(1 << 1.5) }\n", "2:28: constant 1.5 truncated to shift count"),
      ("package main\nfunc main() { f := 1.5; println(f / 0.0) }\n", "2:37: division by zero"),
      ("package main\nfunc main() { println(bool(1)) }\n", "2:28: cannot convert untyped int to bool"),
      ("package main\nfunc main() { println(int(true)) }\n", "2:27: cannot convert bool to int"),
      ("package main\nfunc main() { println(int8(1, 2)) }\n", "2:23: conversion to int8 expects one argument"),
      ("package main\nfunc main() { println(0x1p-2) }\n",
        "2:23: hexadecimal floating-point literals are unsupported"),
      ("package main\nfunc f(s string) {}\nfunc main() {}\n", "2:10: unsupported type 'string'"),
      ("package main\nfunc f() (x int) {}\nfunc main() {}\n", "2:13: named results are unsupported"),
      ("package main\nfunc f() (int, int) { return 1 }\nfunc main() {}\n",
        "2:23: not enough return values in function 'f'"),
      ("package main\nfunc f() (int, int) { return 1, true }\nfunc main() {}\n",
        "2:33: return value must be int"),
      ("package main\nfunc f() (int, int) { return 1, 2 }\nfunc main() { x := f() }\n",
        "3:20: multiple-value f() in single-value context"),
      ("package main\nfunc f() (int, int) { return 1, 2 }\nfunc main() { println(f()) }\n",
        "3:23: multiple-value f() in single-value context"),
      ("package main\nfunc g() int { return 1 }\nfunc main() { a, b := g() }\n",
        "3:23: assignment mismatch: 2 variables but g() returns 1 value"),
      ("package main\nfunc main() { a, b := 1 }\n",
        "2:23: assignment mismatch: 2 variables but 1 value"),
      ("package main\nfunc f() (int, int) { return 1, 2 }\nfunc main() { a, b := f(); a, b := f() }\n",
        "3:28: no new variables on left side of :="),
      ("package main\nfunc f() (int, int) { return 1, 2 }\nfunc main() { _, _ := f() }\n",
        "3:15: no new variables on left side of :="),
      ("package main\nfunc f() (int, int) { return 1, 2 }\nfunc main() { a, a := f() }\n",
        "3:18: 'a' repeated on left side of :="),
      ("package main\nfunc f() (int, int) { return 1, 2 }\nfunc main() { a, b = f() }\n",
        "3:15: unknown identifier 'a'"),
      ("package main\nfunc f() (int, int) { return 1, 2 }\nfunc main() { var a bool; a, b := f() }\n",
        "3:27: assignment type does not match variable type"),
      ("package main\nfunc g() (int, int) { return 1, 2 }\nfunc f() (int, bool) { return g() }\nfunc main() {}\n",
        "3:31: results of g() do not match the results of function 'f'"),
      ("package main\nfunc main() (int, int) { return 1, 2 }\n",
        "2:1: main must have no parameters or return value"),
      ("package main\nfunc f() int { return 1 < 2 }\nfunc main() {}\n", "2:23: return value must be int"),
      ("package main\nfunc f() int { return }\nfunc main() {}\n",
        "2:16: function 'f' must return a value"),
      ("package main\nfunc f() { return 1 }\nfunc main() {}\n",
        "2:19: function 'f' returns no value"),
      ("package main\nfunc main() { if 1 { println(2) } }\n", "2:18: if condition must be bool"),
      ("package main\nfunc f(n int) int { return n }\nfunc main() { println(f(1 < 2)) }\n",
        "3:25: function arguments must be int"),
      ("package main\nfunc main() { println(missing) }\n", "2:23: unknown identifier 'missing'"),
      ("package main\nfunc g(x int) int { return x }\nfunc f(g int) int { return g(g) }\nfunc main() {}\n",
        "3:28: cannot call non-function 'g'"),
      ("package main\nfunc f(println int) int { println(1); return 1 }\nfunc main() {}\n",
        "2:27: cannot call non-function 'println'"),
      ("package main\nfunc f(g int) int { g(1); return 1 }\nfunc main() {}\n",
        "2:21: cannot call non-function 'g'")] do
    let actual := match compileToLLVM (Source.ofString source) with
      | .error diagnostic => diagnostic.render (Source.ofString source)
      | .ok _ => "no error"
    check (actual == expected) s!"wrong lowering error: {source}expected: {expected}\nactual: {actual}"
  IO.println "Go parser and AOT tests: OK"
