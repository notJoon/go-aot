# ABI

How each backend represents Go values at function boundaries and in memory.

The compiler always sees the whole program, and the C and LLVM backends never call into each
other's output, so the two representations only have to agree with themselves. Every decision
here is provisional until issue #14 covers the rest of the language.

## Scalars

| Go type | LLVM | C |
| --- | --- | --- |
| `bool` | `i1` | `int64_t` holding 0 or 1 |
| `int`, `int64` | `i64` | `int64_t` |
| `int8`, `int16`, `int32` | `i8`, `i16`, `i32` | `int8_t`, `int16_t`, `int32_t` |
| `uint`, `uint64` | `i64` | `uint64_t` |
| `uint8`, `uint16`, `uint32` | `i8`, `i16`, `i32` | `uint8_t`, `uint16_t`, `uint32_t` |
| `float64` | `double` | `double` |

`int` and `uint` are 64 bits wide. A C bool is an `int64_t` because a C comparison produces an
`int` holding 0 or 1, which is then stored without conversion.

Parameters are passed as these scalars, in source order.

## Results

A function returns according to how many results it declares.

* **None.** LLVM returns `void` and C returns `void`. `main` has no results in Go but returns a
  zero exit status, `i32 0` in LLVM and `int` 0 in C.
* **One.** The result's scalar is returned directly.
* **Two or more.** The results are packed into one aggregate returned by value.
  * LLVM returns the literal struct `{ T0, T1, ... }` of the result types. The callee builds it
    with `insertvalue` and the caller takes it apart with `extractvalue`. LLVM decides whether the
    struct travels in registers or through a hidden pointer, which is safe because both sides of
    every call come from the same compiler.
  * C returns `struct go_<name>_results { T0 r0; T1 r1; ... }`, one struct per function, named
    after the function's symbol. The callee returns a compound literal and the caller reads the
    fields it uses.

For example, `func split(n int) (int, bool)` is `{ i64, i1 } @go_split(i64)` in LLVM and
`struct go_split_results { int64_t r0; int64_t r1; } go_split(int64_t)` in C.

What would force a change:

* **Calls to or from code this compiler did not build.** Such calls would need the platform C
  calling convention for aggregates. `cgo` is a non-goal.
* **Named results that `defer` and `recover` can modify.** These might need the results in memory
  the callee can reach (issue #24).

## Not decided yet

Strings, slices, interfaces, structs, aggregates passed by value, and symbol mangling are open.
Issue #14 covers them, and #15 covers mangling.
