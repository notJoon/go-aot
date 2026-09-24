/-!
A small test runner. Every case runs, failures are collected instead of stopping the run, and the
summary decides the exit code. `lake test -- --help` lists the options.
-/

namespace GoAot.Tests

inductive Outcome where
  | pass
  | fail (message : String)
  | skip (reason : String)

structure Case where
  /-- A path-like name such as `run/fib` or `gc/fib`, matched by the command line filters. -/
  name : String
  /-- The group `--tier` selects: `unit`, `cases`, `gc`, or `perf`. -/
  tier : String
  /-- Allocation measurements count the whole process, so these cases run alone, first. -/
  exclusive : Bool := false
  run : IO Outcome

structure Options where
  filters : Array String := #[]
  tiers : Array String := #[]
  /-- Rewrite expected output files from the current results instead of comparing. -/
  update : Bool := false
  list : Bool := false
  jobs : Nat := 8

def usage : String := "usage: lake test -- [options] [filter...]

Runs the cases whose name contains any filter, or every case without filters.

  --tier NAME   run only this tier, repeatable: unit, cases, gc, perf
  --update      rewrite .out files from gc, and .ll and .parse files from the compiler
  --list        print the selected case names without running them
  -j N          run N cases at a time (default 8)"

def Options.parse : List String → Options → Except String Options
  | [], options => pure options
  | "--tier" :: tier :: rest, options => Options.parse rest { options with tiers := options.tiers.push tier }
  | "--update" :: rest, options => Options.parse rest { options with update := true }
  | "--list" :: rest, options => Options.parse rest { options with list := true }
  | "-j" :: jobs :: rest, options =>
    match jobs.toNat? with
    | some jobs => if jobs == 0 then throw "-j needs a positive number"
      else Options.parse rest { options with jobs }
    | none => throw s!"-j needs a number, not '{jobs}'"
  | argument :: rest, options =>
    if argument.startsWith "-" then throw s!"unknown option '{argument}'\n\n{usage}"
    else Options.parse rest { options with filters := options.filters.push argument }

def Options.selects (options : Options) (case : Case) : Bool :=
  (options.tiers.isEmpty || options.tiers.contains case.tier) &&
    (options.filters.isEmpty || options.filters.any (case.name.contains ·))

private def attempt (case : Case) : IO Outcome :=
  try case.run catch error => pure (.fail (toString error))

private def indent (text : String) : String :=
  "\n".intercalate ((text.trimAsciiEnd.copy.splitOn "\n").map ("    " ++ ·))

/-- Run the selected cases and report them. Returns the process exit code. -/
def runCases (options : Options) (cases : Array Case) : IO UInt32 := do
  let selected := (cases.filter options.selects).qsort (·.name < ·.name)
  if options.list then
    for case in selected do IO.println case.name
    return 0
  let mut outcomes : Array (Case × Outcome) := #[]
  for case in selected.filter (·.exclusive) do
    outcomes := outcomes.push (case, ← attempt case)
  -- Most cases wait on Clang or Go, so a pool of workers overlaps them.
  let shared := selected.filter (!·.exclusive)
  let next ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate shared.size (none : Option Outcome))
  let workers ← (List.range (min options.jobs shared.size)).mapM fun _ =>
    IO.asTask (prio := .dedicated) do
      repeat
        let index ← next.modifyGet fun index => (index, index + 1)
        let some case := shared[index]? | break
        let outcome ← attempt case
        results.modify (·.set! index (some outcome))
  for worker in workers do IO.ofExcept (← IO.wait worker)
  for case in shared, outcome in ← results.get do
    outcomes := outcomes.push (case, outcome.getD (.fail "case did not finish"))

  let mut passed := 0
  let mut failed := 0
  let mut skipped : Array (String × Nat) := #[]
  for (case, outcome) in outcomes do
    match outcome with
    | .pass => passed := passed + 1
    | .fail message =>
      failed := failed + 1
      IO.println s!"FAIL {case.name}\n{indent message}"
    | .skip reason =>
      skipped := match skipped.findIdx? (·.1 == reason) with
        | some index => skipped.modify index fun (reason, count) => (reason, count + 1)
        | none => skipped.push (reason, 1)
  for (reason, count) in skipped do IO.println s!"skipped {count}: {reason}"
  let total := skipped.foldl (· + ·.2) 0
  IO.println s!"{passed} passed, {failed} failed, {total} skipped"
  return if failed == 0 then 0 else 1

end GoAot.Tests
