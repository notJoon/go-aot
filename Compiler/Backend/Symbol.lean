module

public import Compiler.IR

public section

namespace GoAot.Backend.Symbol

/--
The linker symbol for the Go function `name`. `main` keeps its name, and every other function
gets a `go_` prefix so it cannot clash with runtime or libc symbols.

Example: `Symbol.function "fib"` is `"go_fib"`, and `Symbol.function "main"` is `"main"`.
-/
def function (name : String) : String :=
  if name == "main" then name else "go_" ++ name

/--
Whether `function` is the process entry point, which returns a zero exit status instead of `void`.

Example: `isEntry ⟨"main", #[], .void, #[]⟩` is `true`, and `isEntry ⟨"f", #[], .void, #[]⟩` is `false`.
-/
def isEntry (function : IR.Function) : Bool :=
  function.name == "main"

/--
Whether `function` returns nothing at the ABI level, which holds for every `void` Go function
except the entry point.

Example: `returnsVoid ⟨"f", #[], .void, #[]⟩` is `true`, and `returnsVoid ⟨"main", #[], .void, #[]⟩`
is `false`.
-/
def returnsVoid (function : IR.Function) : Bool :=
  function.returnKind == .void && !isEntry function

end GoAot.Backend.Symbol
