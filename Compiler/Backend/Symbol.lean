module

public import Compiler.IR

public section

namespace GoAot.Backend.Symbol

/-- The linker symbol for the Go function `name`: `main` keeps its name, and every other function
gets a `go_` prefix so it cannot clash with runtime or libc symbols.
`Symbol.function "fib"` is `"go_fib"`; `Symbol.function "main"` is `"main"`. -/
def function (name : String) : String :=
  if name == "main" then name else "go_" ++ name

/-- Whether `function` is the process entry point, which returns a zero exit status instead of
`void`. `isEntry ⟨"main", #[], .void, #[]⟩` is `true`; `isEntry ⟨"f", #[], .void, #[]⟩` is `false`. -/
def isEntry (function : IR.Function) : Bool :=
  function.name == "main"

/-- Whether `function` returns nothing at the ABI level: a `void` Go function that is not the entry.
`returnsVoid ⟨"f", #[], .void, #[]⟩` is `true`; `returnsVoid ⟨"main", #[], .void, #[]⟩` is `false`. -/
def returnsVoid (function : IR.Function) : Bool :=
  function.returnKind == .void && !isEntry function

end GoAot.Backend.Symbol
