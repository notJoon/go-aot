import GoAot
import Compiler.Parser.Go
import Compiler.IR.Verify
import Compiler.Backend.LLVM
import Tests.Harness

/-!
Test cases read from `Tests/Cases`. Each `.go` file starts with `//` directive lines that say what
to check. `Tests/README.md` documents the directives.
-/

open GoAot

namespace GoAot.Tests

def casesRoot : System.FilePath := "Tests/Cases"

inductive Kind where
  /-- Compile, run, and compare stdout with the `.out` file. -/
  | run
  /-- Compilation fails with the diagnostic an `// ERROR` comment names. -/
  | errorcheck
  /-- Parse only, and compare the syntax summary with the `.parse` file. -/
  | parse
  /-- Run, expect exit status 2, this first stderr line, and stdout from the `.out` file if any. -/
  | panic (message : String)

structure Directives where
  kind : Kind
  /-- Compare with gc only on these host architectures. -/
  gcArch : Array String := #[]
  /-- Text the generated LLVM IR must not contain. -/
  irLacks : Array String := #[]
  /-- Text Clang's `-O2` output must contain. -/
  optimizedHas : Array String := #[]
  /-- Text Clang's `-O2` output must not contain. -/
  optimizedLacks : Array String := #[]

/-- Parse the `//` lines before the first other line. -/
def Directives.parse (text : String) : Except String Directives := do
  let mut kind : Option Kind := none
  let mut directives : Directives := { kind := .run }
  for line in text.splitOn "\n" do
    let some body := line.dropPrefix? "//" | break
    let body := body.trimAscii.copy
    let (key, value) := match body.splitOn ":" with
      | key :: rest => (key.trimAscii.copy, (":".intercalate rest).trimAscii.copy)
      | [] => (body, "")
    let setKind (next : Kind) : Except String (Option Kind) :=
      if kind.isSome then throw "a case has one of run, errorcheck, parse, or panic" else pure (some next)
    match key with
    | "run" => kind ← setKind .run
    | "errorcheck" => kind ← setKind .errorcheck
    | "parse" => kind ← setKind .parse
    | "panic" => kind ← setKind (.panic value)
    | "gc-arch" => directives := { directives with gcArch := directives.gcArch.push value }
    | "ir-lacks" => directives := { directives with irLacks := directives.irLacks.push value }
    | "optimized-has" => directives := { directives with optimizedHas := directives.optimizedHas.push value }
    | "optimized-lacks" =>
      directives := { directives with optimizedLacks := directives.optimizedLacks.push value }
    | _ => throw s!"unknown directive '{key}'"
  let some found := kind | throw "the first lines must name run, errorcheck, parse, or panic"
  return { directives with kind := found }

/-- An expected diagnostic: `// ERROR "message"`, or `// ERROR 12 "message"` to also check the column. -/
structure ExpectedError where
  line : Nat
  column : Option Nat
  message : String

def ExpectedError.parse (text : String) : Except String ExpectedError := do
  let lines := text.splitOn "\n"
  let mut found := #[]
  for h : index in [:lines.length] do
    let line := lines[index]
    let parts := line.splitOn "// ERROR "
    if let [_, annotation] := parts then
      let (column, quoted) := match annotation.splitOn " " with
        | first :: rest => match first.toNat? with
          | some column => (some column, " ".intercalate rest)
          | none => (none, annotation)
        | [] => (none, annotation)
      let quoted := quoted.trimAscii.copy
      unless quoted.length ≥ 2 && quoted.startsWith "\"" && quoted.endsWith "\"" do
        throw s!"line {index + 1}: expected // ERROR [column] \"message\""
      found := found.push ⟨index + 1, column, ((quoted.drop 1).dropEnd 1).copy⟩
  match found with
  | #[expected] => return expected
  | #[] => throw "an errorcheck case needs one // ERROR comment"
  | _ => throw "the compiler reports only its first error, so a case has one // ERROR comment"

-- The Lean toolchain Clang on macOS cannot locate the host SDK during linking.
def clangCommand : IO String :=
  return (← IO.getEnv "CLANG").getD (if System.Platform.isOSX then "/usr/bin/clang" else "clang")

-- Verify input SSA and every transformed module before code generation.
def llvmOptions : Array String := #["-Wno-override-module", "-Xclang", "-llvm-verify-each"]

/-- IR that relies on poison or undefined behavior often works at only one of these levels. -/
def optimizationLevels : List String := ["-O0", "-O2"]

def clang (arguments : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := ← clangCommand, args := arguments }
  unless result.exitCode == 0 do throw (IO.userError result.stderr)

def runLLVM (generated : String) (level : String) : IO IO.Process.Output :=
  IO.FS.withTempDir fun dir => do
    let sourcePath := dir / "program.ll"
    let exePath := dir / "program"
    IO.FS.writeFile sourcePath generated
    clang (#[level] ++ llvmOptions ++ #["-x", "ir", sourcePath.toString, "-o", exePath.toString])
    IO.Process.output { cmd := exePath.toString }

def optimizeLLVM (generated : String) : IO String :=
  IO.FS.withTempDir fun dir => do
    let sourcePath := dir / "program.ll"
    let optimizedPath := dir / "optimized.ll"
    IO.FS.writeFile sourcePath generated
    clang (#["-O2"] ++ llvmOptions ++ #["-S", "-emit-llvm", "-x", "ir", sourcePath.toString,
      "-o", optimizedPath.toString])
    IO.FS.readFile optimizedPath

/-- The Go command to compare against, or why gc cases are skipped. -/
structure Gc where
  command? : Except String String

/-- Go 1.26 is the first version checked to print floats in the shortest form the cases use. -/
def Gc.find : IO Gc := do
  let command := (← IO.getEnv "GO").getD "go"
  let version ← try
      let output ← IO.Process.output { cmd := command, args := #["env", "GOVERSION"] }
      pure (if output.exitCode == 0 then output.stdout.trimAscii.copy else "")
    catch _ => pure ""
  -- `go1.26.2` and `go1.26rc1` both have minor version 26.
  let minor := match (version.dropPrefix "go1.").copy.splitOn "." with
    | minor :: _ => (minor.takeWhile Char.isDigit).copy.toNat?
    | [] => none
  if version.startsWith "go1." && minor.any (· ≥ 26) then return ⟨.ok command⟩
  return ⟨.error s!"gc comparison needs go1.26 or later, found '{version}'"⟩

def hostArch : String :=
  let target := System.Platform.target
  if target.startsWith "aarch64" || target.startsWith "arm64" then "arm64"
  else if target.startsWith "x86_64" then "amd64"
  else target

/-- gc's output for a program. Go's `println` writes to stderr. -/
def Gc.output (gc : Gc) (path : System.FilePath) : IO (Except String String) := do
  let .ok command := gc.command? | return .error "Go is unavailable"
  let output ← IO.Process.output { cmd := command, args := #["run", path.toString] }
  if output.exitCode != 0 then return .error s!"go run failed:\n{output.stderr}"
  return .ok output.stderr

private def readIfExists (path : System.FilePath) : IO (Option String) := do
  if ← path.pathExists then return some (← IO.FS.readFile path) else return none

private def renderParse (text : String) : String :=
  match parse (Source.ofString text) with
  | .ok file => Id.run do
    let packageName := file.packageName
    let mut output := s!"package {packageName.text} {packageName.span.start}:{packageName.span.stop}\n"
    for function in file.functions do
      let name := function.name
      output := output ++ s!"func {name.text} {name.span.start}:{name.span.stop} " ++
        s!"{function.span.start}:{function.span.stop}\n"
    return output
  | .error diagnostic => "error " ++ diagnostic.render (Source.ofString text) ++ "\n"

/-- Compare `actual` with an expected file, or write it when updating. -/
private def expectFile (update : Bool) (path : System.FilePath) (actual : String)
    (what : String) : IO (Option String) := do
  if update then
    IO.FS.writeFile path actual
    return none
  match ← readIfExists path with
  | none => return some s!"missing {path}, which --update creates"
  | some expected =>
    if expected == actual then return none
    return some s!"{what} differs from {path}:\n{actual}"

private def check (failures : Array String) (ok : Bool) (message : String) : Array String :=
  if ok then failures else failures.push message

private def outcomeOf (failures : Array String) : Outcome :=
  if failures.isEmpty then .pass else .fail ("\n".intercalate failures.toList)

private def compile (source : Source) : Except String String :=
  (compileToLLVM source).mapError (·.render source)

private def runCase (update : Bool) (gc : Gc) (path : System.FilePath) (text : String)
    (directives : Directives) : IO Outcome := do
  let generated ← match compile (Source.ofString text) with
    | .ok generated => pure generated
    | .error message => return .fail s!"compile failed: {message}"
  let mut failures := #[]
  -- Only cases with an `.ll` file pin their IR. An empty one is filled in by --update.
  let irPath := path.withExtension "ll"
  if ← irPath.pathExists then
    if let some failure ← expectFile update irPath generated "LLVM IR" then failures := failures.push failure
  for text in directives.irLacks do
    failures := check failures (!generated.contains text) s!"LLVM IR contains '{text}'"
  let outPath := path.withExtension "out"
  -- `.out` files hold gc's output, so updating them runs gc rather than this compiler.
  if update && (directives.gcArch.isEmpty || directives.gcArch.contains hostArch) then
    match ← gc.output path with
    | .ok output => IO.FS.writeFile outPath output
    | .error reason => failures := failures.push s!"cannot update {outPath}: {reason}"
  let some expected ← readIfExists outPath | return .fail s!"missing {outPath}"
  for level in optimizationLevels do
    let output ← runLLVM generated level
    failures := check failures (output.exitCode == 0 && output.stdout == expected)
      s!"at {level}, exit {output.exitCode}, expected {outPath}:\n{expected}got:\n{output.stdout}{output.stderr}"
  unless directives.optimizedHas.isEmpty && directives.optimizedLacks.isEmpty do
    let optimized ← optimizeLLVM generated
    for text in directives.optimizedHas do
      failures := check failures (optimized.contains text) s!"optimized IR lacks '{text}'"
    for text in directives.optimizedLacks do
      failures := check failures (!optimized.contains text) s!"optimized IR contains '{text}'"
  return outcomeOf failures

private def panicCase (path : System.FilePath) (text : String) (message : String) : IO Outcome := do
  let generated ← match compile (Source.ofString text) with
    | .ok generated => pure generated
    | .error message => return .fail s!"compile failed: {message}"
  let expected := (← readIfExists (path.withExtension "out")).getD ""
  let stderr := s!"panic: {message}\n"
  let mut failures := #[]
  for level in optimizationLevels do
    let output ← runLLVM generated level
    failures := check failures (output.exitCode == 2 && output.stdout == expected && output.stderr == stderr)
      s!"at {level}: exit {output.exitCode}, stdout {repr output.stdout}, stderr {repr output.stderr}"
  return outcomeOf failures

private def errorCase (text : String) : IO Outcome := do
  let expected ← match ExpectedError.parse text with
    | .ok expected => pure expected
    | .error message => return .fail message
  let source := Source.ofString text
  let .error diagnostic := compileToLLVM source | return .fail "compiled without an error"
  let position := diagnostic.span?.bind (source.position? ·.start)
  let actual := diagnostic.render source
  let lineMatches := position.any (·.line == expected.line)
  let columnMatches := expected.column.all fun column => position.any (·.column == column)
  if lineMatches && columnMatches && diagnostic.message == expected.message then return .pass
  let column := (expected.column.map (s!":{·}")).getD ""
  return .fail s!"expected {expected.line}{column}: {expected.message}\ngot      {actual}"

private def parseCase (update : Bool) (path : System.FilePath) (text : String) : IO Outcome := do
  match ← expectFile update (path.withExtension "parse") (renderParse text) "parse summary" with
  | some failure => return .fail failure
  | none => return .pass

private def gcCase (update : Bool) (gc : Gc) (path : System.FilePath) (directives : Directives) :
    IO Outcome := do
  -- The run case writes the `.out` file from gc when updating, so there is nothing to compare.
  if update then return .skip "--update writes .out files from gc"
  if let .error reason := gc.command? then return .skip reason
  unless directives.gcArch.isEmpty || directives.gcArch.contains hostArch do
    return .skip s!"gc output differs on {hostArch}"
  let expected ← IO.FS.readFile (path.withExtension "out")
  match ← gc.output path with
  | .error reason => return .fail reason
  | .ok output =>
    if output == expected then return .pass
    return .fail s!"gc prints something other than the .out file:\n{output}"

/-- Every case under `Tests/Cases`, plus a gc comparison for each `run` case. -/
def fileCases (options : Options) (gc : Gc) : IO (Array Case) := do
  let files ← casesRoot.walkDir
  let mut cases := #[]
  for path in files.qsort (·.toString < ·.toString) do
    unless path.extension == some "go" do continue
    let name := ((path.toString.dropPrefix (casesRoot.toString ++ "/")).dropEnd 3).copy
    let text ← IO.FS.readFile path
    match Directives.parse text with
    | .error message => cases := cases.push ⟨name, "cases", false, pure (.fail message)⟩
    | .ok directives =>
      let run : IO Outcome := match directives.kind with
        | .run => runCase options.update gc path text directives
        | .errorcheck => errorCase text
        | .parse => parseCase options.update path text
        | .panic message => panicCase path text message
      cases := cases.push ⟨name, "cases", false, run⟩
      if directives.kind matches .run then
        cases := cases.push ⟨"gc/" ++ name, "gc", false, gcCase options.update gc path directives⟩
  return cases

/-- Checks of the LLVM toolchain setup and of IR that no source program produces. -/
def llvmCases : Array Case := #[
  ⟨"llvm/rejects-invalid-ssa", "cases", false, do
    IO.FS.withTempDir fun dir => do
      let objectPath := dir / "invalid.o"
      let result ← IO.Process.output {
        cmd := ← clangCommand
        args := #["-O2"] ++ llvmOptions ++ #["-x", "ir", "-c", "Tests/Fixtures/invalid_ssa.ll",
          "-o", objectPath.toString]
      }
      return if result.exitCode != 0 then .pass else .fail "LLVM verifier accepted invalid SSA"⟩,
  ⟨"llvm/direct-cfg", "cases", false, do
    -- Backward and conditional edges between blocks, in an order no lowering produces.
    let program : IR.Program := ⟨#[
      ⟨"main", #[], #[], #[⟨#[.call #[0] "walk" #[], .print .int (.value 0)], .ret #[]⟩]⟩,
      ⟨"walk", #[], #[.int], #[
        ⟨#[], .br 2⟩,
        ⟨#[.print .int (.literal 11)], .ret #[(.literal 7)]⟩,
        ⟨#[.binary 0 .less .int (.literal 1) (.literal 0)], .condBr (.value 0) 2 1⟩,
        ⟨#[], .br 3⟩]⟩]⟩
    let .ok () := IR.verify program | return .fail "valid cyclic CFG rejected"
    let output ← runLLVM (Backend.LLVM.emit program) "-O2"
    return if output.exitCode == 0 && output.stdout == "11\n7\n" then .pass
      else .fail s!"wrong output {repr output.stdout}"⟩]

end GoAot.Tests
