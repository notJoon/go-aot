# GoAot

## Why did I start this?

Just for fun. Honestly, using Lean probably does not make this project any better. Rust or OCaml would be a better choice.

## Goals and non-goals

I do not intend to implement all of Go, so the goals and non-goals of this project are:

### Goals

1. Integers, strings, slices, structs, pointers, functions, methods, and interfaces
2. Closures, `defer`, `panic`, and `recover`
3. Goroutines and channels, with `select` being optional
4. Only a tiny, hand-written standard library, such as `fmt.Println` and a few other functions. `import` will either be unsupported or limited to built-in packages
5. The project is considered successful if around five benchmark programs produce the same results as `gc`

### Non-goals

Generics, reflection, `cgo`, randomized map iteration, a complete implementation of `select`, precise garbage collection, and so on.

I may change my mind and implement some of these later, but they are not goals for now.

## Structure

![Structure](structure_adr.JPG)

Compilation parses source into syntax, checks names and types into a resolved tree,
then lowers that tree to IR. IR verification runs before the LLVM backend.

## Backends

The compiler emits target independent LLVM IR and asks Clang to optimize, generate host
machine code, and link it. It invokes `clang -O2 -x ir`, or the Clang that `CLANG` names, and
the generated IR contains no hard-coded target triple or data layout.

LLVM is the only backend. A C backend served as a second implementation to compare against
while the language core was built, and was removed once the core was complete (#13). It shares
the parser, checker, lowering, and IR with the LLVM backend, so comparing the two only caught
code generation differences. Every feature had to be written twice, and the runtime work ahead,
such as precise stack maps for the collector, unwinding, and goroutines, relies on LLVM features
C cannot express.

Correctness is measured against gc instead. The expected output of every test program is
what gc's build of it prints, and `lake test` runs each program with `go run` to confirm this
when Go is installed.

Values are `bool`, `int`, `int8` to `int64`, `uint`, `uint8` to `uint64`, and `float64`.
Functions can return several results. [docs/ABI.md](docs/ABI.md) records how values,
parameters, and results are represented, and the layouts decided for later types.

Untyped constants are exact, as in Go, and take their type from the context or default to
`int` or `float64`. A constant that overflows its type or truncates a fraction is a compile
error. Expressions on typed constants, such as `int8(100) * 2`, are not folded, so they wrap at
run time where Go reports an overflow. Hexadecimal float literals and the `byte` and `rune`
aliases are not supported yet.

Integer arithmetic wraps at the width of its type. Division and remainder follow Go. Dividing by a constant zero is a compile error. Dividing by
zero at run time flushes stdout, writes `panic: runtime error: integer divide by zero` to
stderr, and exits with status 2. Go also prints a goroutine trace, which this runtime does not
have. The most negative value divided by -1 wraps to itself with remainder 0. A shift by a
count at or above the width gives 0, or -1 for a negative signed value shifted right, and a
negative count panics with `panic: runtime error: negative shift amount`.

Converting a float to an integer truncates toward zero. Go leaves out of range results to the
implementation. Like gc on arm64, the conversion saturates at the target range, NaN becomes 0,
and a target narrower than 32 bits saturates at 32 bits and then truncates, so `uint8(300.0)`
is 44.

`println` prints a float64 as Go does, the shortest digits that round trip in `%e` form when the
exponent is below -4 or at least 6: `0.3`, `1.23456789e+08`, `-0`, `+Inf`, `NaN`.

## How to Run

Compile a Go file and run the program:

	lake exe goaot Tests/Cases/run/hello.go -o hello
	./hello

An output ending in `.ll` saves the generated LLVM IR instead of building a program:

	lake exe goaot input.go -o program.ll

Run the tests. [Tests/README.md](Tests/README.md) describes the test cases, how to run a subset,
and how to update expected files:

	lake test
