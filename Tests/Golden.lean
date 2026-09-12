import GoAot

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
  | .error message => "error " ++ message ++ "\n"

private def checkGolden (name : String) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let input ← IO.FS.readFile (path ++ ".go")
  let expected ← IO.FS.readFile (path ++ ".golden")
  let actual := renderParse input
  check (actual == expected) s!"golden mismatch: {name}\nexpected:\n{expected}actual:\n{actual}"

private def checkCompileGolden (name : String) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let input ← IO.FS.readFile (path ++ ".go")
  let expected ← IO.FS.readFile (path ++ ".c.golden")
  let expectedOutput ← IO.FS.readFile (path ++ ".out.golden")
  match compileToC (Source.ofString input) with
  | .ok actual =>
    check (actual == expected) s!"compile golden mismatch: {name}\n{actual}"
    IO.FS.withTempDir fun dir => do
      let cPath := dir / "program.c"
      let exePath := dir / "program"
      IO.FS.writeFile cPath actual
      discard <| IO.Process.run { cmd := "cc", args := #[cPath.toString, "-o", exePath.toString] }
      let output ← IO.Process.run { cmd := exePath.toString }
      check (output == expectedOutput) s!"wrong native output: {repr output}"
  | .error message => throw (IO.userError s!"compile failed: {name}: {message}")

-- The Lean toolchain Clang on macOS cannot locate the host SDK during linking.
private def clangCommand : String :=
  if System.Platform.isOSX then "/usr/bin/clang" else "clang"

-- Verify input SSA and every transformed module before code generation.
private def llvmOptions : Array String :=
  #["-O2", "-Wno-override-module", "-Xclang", "-llvm-verify-each"]

private def runGenerated (command language : String) (options : Array String)
    (generated : String) : IO IO.Process.Output :=
  IO.FS.withTempDir fun dir => do
    let sourcePath := dir / "program"
    let exePath := dir / "executable"
    IO.FS.writeFile sourcePath generated
    let args := options ++ #["-x", language, sourcePath.toString, "-o", exePath.toString]
    let result ← IO.Process.output { cmd := command, args }
    unless result.exitCode == 0 do throw (IO.userError result.stderr)
    IO.Process.output { cmd := exePath.toString }

private def checkLLVM (name : String) (golden : Bool := false) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let input ← IO.FS.readFile (path ++ ".go")
  let expectedOutput ← IO.FS.readFile (path ++ ".out.golden")
  match compileToLLVM (Source.ofString input) with
  | .ok actual =>
    if golden then
      let expected ← IO.FS.readFile (path ++ ".ll.golden")
      check (actual == expected) s!"LLVM golden mismatch: {name}\n{actual}"
    IO.FS.withTempDir fun dir => do
      let llvmPath := dir / "program.ll"
      let optimizedPath := dir / "optimized.ll"
      let exePath := dir / "program"
      IO.FS.writeFile llvmPath actual
      let compileArgs := llvmOptions ++ #["-x", "ir", llvmPath.toString, "-o", exePath.toString]
      discard <| IO.Process.run { cmd := clangCommand, args := compileArgs }
      let output ← IO.Process.run { cmd := exePath.toString }
      check (output == expectedOutput) s!"wrong LLVM output: {name}: {repr output}"
      if name == "hello" then
        let optimizeArgs := llvmOptions ++ #["-S", "-emit-llvm", "-x", "ir", llvmPath.toString,
          "-o", optimizedPath.toString]
        discard <| IO.Process.run { cmd := clangCommand, args := optimizeArgs }
        let optimized ← IO.FS.readFile optimizedPath
        check (optimized.contains "target datalayout") "optimized LLVM IR has no data layout"
        check (optimized.contains "target triple") "optimized LLVM IR has no target triple"
  | .error message => throw (IO.userError s!"LLVM compile failed: {name}: {message}")

private def checkSameRejection (source : String) : IO Unit :=
  match compileToC (Source.ofString source), compileToLLVM (Source.ofString source) with
  | .error c, .error llvm => check (c == llvm) s!"backend errors differ: {c} / {llvm}"
  | _, _ => throw (IO.userError "C and LLVM did not reject the same invalid source")

-- Compare runtime behavior directly because IR goldens only protect emitter formatting.
private def checkDifferential (name : String) : IO Unit := do
  let path := "Tests/Golden/" ++ name
  let source := Source.ofString (← IO.FS.readFile (path ++ ".go"))
  let expected ← IO.FS.readFile (path ++ ".out.golden")
  let .ok c := compileToC source | throw (IO.userError s!"C rejected {name}")
  let .ok llvm := compileToLLVM source | throw (IO.userError s!"LLVM rejected {name}")
  let cOutput ← runGenerated "cc" "c" #["-O2", "-std=c11"] c
  let llvmOutput ← runGenerated clangCommand "ir" llvmOptions llvm
  check (cOutput.exitCode == llvmOutput.exitCode) s!"backend exit codes differ: {name}"
  check (cOutput.stdout == llvmOutput.stdout) s!"backend stdout differs: {name}"
  check (llvmOutput.exitCode == 0 && llvmOutput.stdout == expected) s!"wrong output: {name}"

-- Byte comparison makes embedded NUL truncation observable.
private def checkNulString : IO Unit := do
  let input ← IO.FS.readFile "Tests/Golden/nul.go"
  let .ok c := compileToC (Source.ofString input)
    | throw (IO.userError "C rejected the NUL string regression fixture")
  let .ok llvm := compileToLLVM (Source.ofString input)
    | throw (IO.userError "LLVM rejected the NUL string regression fixture")
  let cOutput ← runGenerated "cc" "c" #["-O2", "-std=c11"] c
  let llvmOutput ← runGenerated clangCommand "ir" llvmOptions llvm
  let expected := ByteArray.mk #[97, 0, 98, 10]
  check (cOutput.exitCode == 0 && cOutput.stdout.toUTF8 == expected) "C changed NUL bytes"
  check (llvmOutput.exitCode == 0 && llvmOutput.stdout.toUTF8 == expected) "LLVM changed NUL bytes"

private def checkInvalidSSARejected : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let llvmPath := dir / "invalid.ll"
    let objectPath := dir / "invalid.o"
    IO.FS.writeFile llvmPath (← IO.FS.readFile "Tests/Golden/invalid_ssa.ll")
    let result ← IO.Process.output {
      cmd := clangCommand
      args := llvmOptions ++ #["-x", "ir", "-c", llvmPath.toString, "-o", objectPath.toString]
    }
    check (result.exitCode != 0) "LLVM verifier accepted invalid SSA"

def goldenMain : IO Unit := do
  checkGolden "minimal"
  checkGolden "invalid"
  checkCompileGolden "hello"
  checkCompileGolden "fib"
  checkCompileGolden "tail_add"
  checkLLVM "hello" true
  checkLLVM "generic_if" true
  checkLLVM "tail_add" true
  checkLLVM "fib" true
  checkLLVM "semantics"
  checkLLVM "strings"
  -- C signed overflow is undefined so LLVM uses an independent expected result.
  checkLLVM "overflow"
  checkDifferential "hello"
  checkDifferential "fib"
  checkDifferential "tail_add"
  checkDifferential "generic_if"
  checkDifferential "semantics"
  checkDifferential "strings"
  checkNulString
  checkInvalidSSARejected
  checkSameRejection "package main\nfunc main() { println(missing()) }\n"
  checkSameRejection "package main\nfunc f(n int) int { return n }\nfunc main() { println(f()) }\n"
  checkSameRejection "package main\nfunc main() { println(9223372036854775808) }\n"
  IO.println "Go parser and AOT tests: OK"
