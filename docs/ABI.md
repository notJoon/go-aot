# ABI

How Go values are laid out in memory and passed between functions in the LLVM IR this compiler
emits.

**Status.** Scalars and results are implemented. Strings, slices, interfaces, structs, and
aggregate parameters are decided but not implemented. They take effect when their issues land.
Everything here is provisional. Each section says what would force a change.

**Assumptions.**

* **Whole program.** The compiler always sees the whole program, and nothing else calls into
  its output except the C runtime entry point `main`. Matching gc's register ABI or the platform
  C convention is therefore not required. Interoperating with either is a non-goal, like `cgo`.
* **64-bit targets only.** A pointer and a *word* are 8 bytes, `int` and `uint` are 64 bits, and
  every scalar is aligned to its size. The data layouts of Clang's 64-bit targets agree with gc
  on these alignments. On arm64 macOS the layout is `e-m:o-i64:64-i128:128-n32:64-S128-Fn32`.
  A 32-bit target would change `int`, `uint`, and every word below.

Offsets below are in bytes.

## Scalars

| Go type | LLVM | Size and alignment |
| --- | --- | --- |
| `bool` | `i1` | 1 |
| `int8`, `uint8` | `i8` | 1 |
| `int16`, `uint16` | `i16` | 2 |
| `int32`, `uint32` | `i32` | 4 |
| `int`, `int64`, `uint`, `uint64` | `i64` | 8 |
| `float64` | `double` | 8 |
| pointer | `ptr` | 8 |

A bool in memory is one byte holding 0 or 1, which is the store size of `i1`. Signedness is not
part of the LLVM type. Instructions choose it, for example `sdiv` or `udiv`, `sext` or `zext`,
and `icmp slt` or `icmp ult`.

## Strings

A string is two words, `{ ptr, i64 }`: a pointer to the bytes, then the length in bytes.

| Offset | Field |
| --- | --- |
| 0 | `data`, pointer to the first byte |
| 8 | `len`, byte count, `i64` |

Size 16, alignment 8, the same as gc.

* **Not null terminated.** A substring shares its parent's bytes, so a terminator cannot be
  guaranteed. Only C interop would need one, and that is a non-goal.
* **Read only.** The bytes are never written, so strings are safe to share.
* **Empty string.** The empty string has `len` 0 and any `data`, including null.
* **Literals.** Literal bytes are private `unnamed_addr` constant arrays, deduplicated per
  program. See the section below for the extra byte they currently carry.

Would change if: string headers need a third word, which nothing planned requires.

## Slices

A slice is three words, `{ ptr, i64, i64 }`: a pointer to the first element, the length, and
the capacity.

| Offset | Field |
| --- | --- |
| 0 | `data`, pointer to element 0 |
| 8 | `len`, `i64` |
| 16 | `cap`, `i64` |

Size 24, alignment 8, the same as gc. A nil slice is `{ null, 0, 0 }`. Elements are laid out
contiguously at the element type's size, which a later struct rule rounds up to its alignment.

Would change if: a collector needs slices to point at object headers instead of elements. The
shadow stack and stack maps planned in issues #26 and #27 accept interior pointers.

## Interfaces

An interface is two words, `{ ptr, ptr }`.

| Offset | Non-empty interface | Empty interface `any` |
| --- | --- | --- |
| 0 | `itab`, pointer to the method table | `type`, pointer to the dynamic type's descriptor |
| 8 | `data` | `data` |

Size 16, alignment 8, the same as gc. A nil interface is `{ null, null }`.

* **`data` word.** It holds the value itself when the dynamic type is pointer shaped, meaning a
  pointer or a one-word type made of one pointer. Otherwise it points to a heap copy of the
  value, so assigning a value to an interface copies it.
* **`itab`.** One is emitted per pair of concrete type and interface, laid out as follows:

  | Offset | Field |
  | --- | --- |
  | 0 | pointer to the interface type descriptor |
  | 8 | pointer to the concrete type descriptor |
  | 16 + 8 × i | pointer to method i, with methods sorted by name as gc sorts them |

  A method receives the `data` word as its receiver argument. Value receivers of types that are
  not pointer shaped get a wrapper that loads the value first.

Would change if: type descriptors (issue #25) need to live at a fixed offset in every itab for
type switches, or dynamic interface conversions need a hash field, as gc's itab has.

## Structs and arrays

Structs use gc's layout, which is also the natural layout of LLVM's non-packed literal structs on
the targets above:

* Fields are placed in declaration order. The compiler never reorders them.
* Each field starts at the next offset that is a multiple of its alignment.
* A struct is aligned to its most aligned field, or 1 when it has none.
* The size is rounded up to a multiple of the alignment.
* A zero-size struct, such as `struct{}` or `[0]int`, has size 0.
* A zero-size **last** field in a struct that is not itself zero size gets one byte of padding
  before the final rounding. A pointer to that field then stays inside the object, which gc
  requires and C does not do. For example, `struct { x int32; z struct{} }` is 8 bytes in gc and
  4 in C. The LLVM type spells this padding out as an explicit `[1 x i8]` field.

An array `[n]T` is `[n x T]`, with size `n` times the size of `T` and the alignment of `T`.

Example: `struct { a bool; b int64; c int16 }` is `{ i1, i64, i16 }`. The fields sit at offsets
0, 8, and 16, and the struct has size 24 and alignment 8, in both gc and LLVM.

Would change if: a target's LLVM data layout aligns a scalar differently from gc, or field
reordering becomes worth its cost. Go does not forbid reordering, but gc never does it.

## Parameters

Parameters are passed in source order, with LLVM's default calling convention. Every function
except `main` has `internal` linkage.

* Scalars and pointers are passed as themselves.
* An aggregate of at most four words (32 bytes) is passed by value as an LLVM first-class
  aggregate. This covers strings, slices, interfaces, and small structs and arrays.
* A larger aggregate is passed as a `ptr` to a copy the caller makes for the call. The callee
  may modify it, which preserves Go's value semantics. LLVM would otherwise split a large
  first-class aggregate into one argument per field.

Would change if: benchmarks show a better threshold, or escape analysis (issue #20) lets the
caller skip the copy when the argument is dead after the call.

## Results

A function returns according to how many results it declares.

* **None.** The function returns `void`. `main` has no results in Go but returns a zero exit
  status, `i32 0`.
* **One.** The result is returned as itself, whether scalar or aggregate.
* **Two or more.** The results are packed into one literal struct `{ T0, T1, ... }` returned by
  value. The callee builds it with `insertvalue` and the caller takes it apart with
  `extractvalue`.

A result or pack of results too large for the target's return registers comes back through a
hidden pointer to memory the caller provides. LLVM's code generator does this demotion itself,
so the IR never spells out `sret`. This is safe because both sides of every call come from this
compiler.

Example: `func split(n int) (int, bool)` is `define internal { i64, i1 } @go_split(i64 %arg0)`.

Would change if: `defer` and `recover` need to modify named results after a panic (issue #24),
which needs the results in memory the callee's deferred calls can reach. Returning very large
arrays would also change it, because they build long `insertvalue` chains.

## Symbols

| Entity | Symbol |
| --- | --- |
| Go function `f` | `@go_f` |
| `main` | `@main` |
| Runtime helpers | `@goaot.<name>`, for example `@goaot.print_line` and `@goaot.div` |
| String literal bytes | `@.str.<n>`, private |
| Other runtime constants | `@.<name>`, private, for example `@.int_format` |

A Go identifier cannot contain `.`, so runtime names never collide with `go_` names. For now,
functions and parameters are limited to ASCII letters, digits, and `_` by `IR.validName`.

Issue #15 decides mangling. With only an LLVM backend, it can use quoted LLVM names, which may
contain any bytes. The direction is `@"go.<package>.<name>"` for functions and
`@"go.<package>.<Type>.<method>"` for methods, which leaves room for package qualification.

## Where the backend differs from this document

The LLVM backend was checked against every implemented section, meaning scalars, results,
symbols, and string literal bytes.

* **String literal globals end with an extra `\00` byte** that the length does not count. This
  fits the rules above, because strings are not guaranteed to be null terminated. It is a leftover
  and can be dropped when strings become values.

Nothing else differs. Strings as values, slices, interfaces, structs, arrays, and aggregate
parameters do not exist yet, so there is nothing further to compare.
