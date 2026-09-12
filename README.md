# GoAot

## Structure

![Structure](structure_adr.JPG)

## Backends

The CLI temporarily uses the C backend by default while the LLVM path is validated.
The LLVM backend emits target independent LLVM IR and asks Clang to optimize,
generate host machine code, and link it. After the correctness and benchmark gates
in `LLVM_BACKEND_PLAN.md` are complete, LLVM becomes the only backend and the C
backend is removed.

	lake exe goaot input.go -o program --backend llvm
	lake exe goaot input.go -o program --backend c

The LLVM backend supports signed 64-bit integers and any number of integer function
arguments. It invokes `clang -O2 -x ir`; generated IR contains no hard-coded target
triple or data layout. The temporary C backend uses the system `cc`.

## MVP

The MVP follows the ADR vertically as
`Driver → Syntax/Parser → Binding+Type+Lowering → IR → C/LLVM IR → host compiler`.
It currently supports `int` functions, parameters, returns, `if`, recursive calls,
`+`, `-`, `<`, and `println` for strings and integers.

`int` is a signed 64-bit value with wrapping add/subtract. Function arguments and
binary operands are evaluated left to right. Locals, assignment, loops, `else`, raw
strings, and other Go constructs are rejected. The temporary C backend is not the
oracle for overflow because signed overflow is undefined in C.

	lake exe goaot Tests/Golden/hello.go -o hello
	./hello
