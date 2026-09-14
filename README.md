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

## Backends

The CLI temporarily uses the C backend by default while the LLVM path is validated.
The LLVM backend emits target independent LLVM IR and asks Clang to optimize,
generate host machine code, and link it. After the correctness and benchmark gates
are complete, LLVM becomes the only backend and the C backend is removed.

	lake exe goaot input.go -o program --backend llvm
	lake exe goaot input.go -o program --backend c

The LLVM backend supports signed 64-bit integers and any number of integer function
arguments. It invokes `clang -O2 -x ir`; generated IR contains no hard-coded target
triple or data layout. The temporary C backend uses the system `cc`. Tests honor
`CC` and `CLANG` to select the host compilers.

## MVP

The MVP follows the ADR vertically as
`Driver → Syntax/Parser → Binding+Type+Lowering → IR → C/LLVM IR → host compiler`.
It currently supports `int` functions, parameters, returns, `if`, recursive calls,
`+`, `-`, `<`, and `println` for strings and integers.

Identifiers resolve through nested scopes (`Compiler/Scope.lean`): parameters
live in the function body's scope, and each `if` body gets a child scope.

`int` is a signed 64-bit value with wrapping add/subtract. Function arguments and
binary operands are evaluated left to right. Locals, assignment, loops, `else`, raw
strings, and other Go constructs are rejected. The temporary C backend is not the
oracle for overflow because signed overflow is undefined in C.

	lake exe goaot Tests/Golden/hello.go -o hello
	./hello
