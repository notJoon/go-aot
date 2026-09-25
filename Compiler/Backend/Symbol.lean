module

public import Compiler.IR

public section

namespace GoAot.Backend.Symbol

/--
Appends `bytes` as the inside of an LLVM quoted string: printable ASCII other than `"` and `\`
stays, and every other byte becomes `\` and two hex digits. Distinct bytes give distinct text.

Example: the bytes of `a"가` append `a\22\EA\B0\80`.
-/
def escape (output : String) (bytes : ByteArray) : String := Id.run do
  let mut output := output
  for byte in bytes do
    let value := byte.toNat
    if 32 <= value && value <= 126 && value != 34 && value != 92 then
      output := output.push (Char.ofNat value)
    else
      output := (output.push '\\').push (value / 16).digitChar.toUpper
      output := output.push (value % 16).digitChar.toUpper
  return output

private def plain (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_'

/--
The LLVM global for the Go function `name`. `main` keeps its name, and every other function gets
a `go_` prefix so it cannot clash with runtime or libc symbols. A name with characters outside
ASCII letters, digits, and `_` is quoted, which lets any Go identifier through as its UTF-8 bytes.
Distinct names give distinct globals: the prefix and the escaping are both reversible, and only
`main` lacks the prefix.

Example: `Symbol.function "fib"` is `@go_fib`, `Symbol.function "main"` is `@main`, and
`Symbol.function "계산"` is `@"go_\EA\B3\84\EC\82\B0"`.
-/
def function (name : String) : String :=
  let symbol := if name == "main" then name else "go_" ++ name
  if symbol.all plain then "@" ++ symbol else escape "@\"" symbol.toUTF8 ++ "\""

/--
Whether `function` is the process entry point, which returns a zero exit status instead of `void`.

Example: `isEntry ⟨"main", #[], #[], #[]⟩` is `true`, and `isEntry ⟨"f", #[], #[], #[]⟩` is `false`.
-/
def isEntry (function : IR.Function) : Bool :=
  function.name == "main"

/--
Whether `function` returns nothing at the ABI level, which holds for every `void` Go function
except the entry point.

Example: `returnsVoid ⟨"f", #[], #[], #[]⟩` is `true`, and `returnsVoid ⟨"main", #[], #[], #[]⟩`
is `false`.
-/
def returnsVoid (function : IR.Function) : Bool :=
  function.results.isEmpty && !isEntry function

end GoAot.Backend.Symbol
