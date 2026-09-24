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
then lowers that tree to IR. IR verification runs before either backend.

## Backends

The CLI temporarily uses the C backend by default while the LLVM path is validated.
The LLVM backend emits target independent LLVM IR and asks Clang to optimize,
generate host machine code, and link it. After the correctness and benchmark gates
are complete, LLVM becomes the only backend and the C backend is removed.

Values are `bool`, `int`, `int8` to `int64`, `uint`, `uint8` to `uint64`, and `float64`.
`int` and `uint` are 64 bits wide. LLVM uses `i1`, the integer of each width, and `double`.
C uses the matching `<stdint.h>` type and `double`, and an `int64_t` holding 0 or 1 for a
bool, which is what a C comparison produces. The two backends never call each other, so their
representations do not have to match.

Untyped constants are exact, as in Go, and take their type from the context or default to
`int` or `float64`. A constant that overflows its type or truncates a fraction is a compile
error. Expressions on typed constants, such as `int8(100) * 2`, are not folded, so they wrap at
run time where Go reports an overflow. Hexadecimal float literals and the `byte` and `rune`
aliases are not supported yet.

Integer arithmetic wraps at the width of its type in both backends. C computes `+`, `-`, `*`,
and bitwise operators on `uint64_t` and converts back, because C leaves signed overflow undefined.
Division and remainder follow Go. Dividing by a constant zero is a compile error. Dividing by
zero at run time flushes stdout, writes `panic: runtime error: integer divide by zero` to
stderr, and exits with status 2. Go also prints a goroutine trace, which this runtime does not
have. The most negative value divided by -1 wraps to itself with remainder 0. A shift by a
count at or above the width gives 0, or -1 for a negative signed value shifted right, and a
negative count panics with `panic: runtime error: negative shift amount`.

Converting a float to an integer truncates toward zero. Go leaves out of range results to the
implementation. Like gc on arm64, both backends saturate at the target range, NaN becomes 0,
and a target narrower than 32 bits saturates at 32 bits and then truncates, so `uint8(300.0)`
is 44.

`println` prints a float64 as Go does, the shortest digits that round trip in `%e` form when the
exponent is below -4 or at least 6: `0.3`, `1.23456789e+08`, `-0`, `+Inf`, `NaN`.

The LLVM backend invokes `clang -O2 -x ir`; generated IR contains no hard-coded target
triple or data layout. The temporary C backend uses the system `cc`.

## How to Run

Compile a Go file and run the program:

	lake exe goaot Tests/Golden/hello.go -o hello
	./hello

Select a backend with `--backend`:

	lake exe goaot input.go -o program --backend llvm
	lake exe goaot input.go -o program --backend c

An output ending in `.ll` or `.c` saves the generated LLVM IR or C code instead of building a program:

	lake exe goaot input.go -o program.ll
	lake exe goaot input.go -o program.c

Run the tests. `CC` and `CLANG` select the host compilers:

	lake test
