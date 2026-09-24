# Tests

`lake test` builds the test driver, then runs every test case and prints each failure followed by a
summary. It exits with status 1 when a case fails.

* **`#guard` checks.** These are in `Tests/*.lean` and run while the driver builds. A failing
  guard is a build error.
* **Cases.** These are files under `Tests/Cases`, described below.
* **gc comparisons.** Each `run` case is also run with `go run`. gc must print exactly its
  `.out` file, because the expected output of every program is gc's.
* **Budgets.** These are allocation budgets for the lexer, checker, lowering, and verifier.

## Running

	lake test                          # everything
	lake test -- fib operators         # cases whose name contains fib or operators
	lake test -- --tier cases          # one tier: unit, cases, gc, or perf
	lake test -- --list errors/        # names only
	lake test -- --update              # rewrite expected files, then review the diff

`CLANG` selects the host Clang. `GO` selects the Go command for the gc comparison, which needs
Go 1.26 or later and is skipped without it.

`--update` rewrites expected files from the following sources:

* **`.out` files** come from gc, never from this compiler, so an update cannot turn a
  miscompilation into the expected output.
* **`.ll` and `.parse` files** come from the compiler.

To pin a new program's LLVM IR, create an empty `.ll` file next to it and run `--update`.

## Cases

A case is a `.go` file under `Tests/Cases`, named by its path without `.go`, such as `run/fib`.
The `//` lines at the top of the file are directives. Exactly one of them gives the kind.

| Kind | Checks |
| --- | --- |
| `// run` | The program compiles and prints its `.out` file at both `-O0` and `-O2`. If a `.ll` file exists, the IR must match it. |
| `// errorcheck` | Compilation fails with the error that the file's one `// ERROR` comment names. |
| `// panic: MESSAGE` | The program exits with status 2 and prints `panic: MESSAGE` to stderr. Its stdout must match the `.out` file, or be empty when there is none. |
| `// parse` | The file's syntax summary, or its parse error, matches the `.parse` file. |

`run` cases take further directives. Each one can appear more than once.

| Directive | Checks |
| --- | --- |
| `// ir-lacks: TEXT` | The generated IR does not contain the text, for example code after a `return`. |
| `// optimized-has: TEXT` | Clang's `-O2` output contains the text. |
| `// optimized-lacks: TEXT` | Clang's `-O2` output does not contain the text. |
| `// gc-arch: ARCH` | Compare with gc only on these host architectures (`arm64`, `amd64`), for behavior Go leaves to the implementation. |

An `errorcheck` file marks the line where the error is reported:

	x := 1 + true // ERROR "operator + is not defined on bool"
	println(1 + true) // ERROR 14 "operator + is not defined on bool"

The message must match exactly. Give the column (a one-based byte column) only when the line
alone does not say where the error is. The compiler stops at its first error, so a file has
one `// ERROR` comment.

The directories group cases by kind: `run`, `errors`, `panics`, and `parse`. A directory does
not decide what a case checks; its directives do.

`Tests/Fixtures` holds inputs that are not Go programs, such as invalid LLVM IR the toolchain
must reject.
