module

public section

namespace Parser

inductive Error where
  | eof
  | other (s: String)
deriving Repr

instance : ToString Error where
  toString
    | .eof => "unexpected end of input"
    | .other s => s

inductive Result (α : Type) (ι : Type) where
  | ok (pos : ι) (res : α)
  | err (pos : ι) (err : Error)

end Parser

@[expose]
def Parse (ι : Type) (α : Type) : Type :=
  ι -> Parser.Result α ι

namespace Parser

class Iterator (ι : Type) (elem : outParam Type) (idx : outParam Type) [DecidableEq idx] [DecidableEq elem] where
  pos : ι -> idx
  hasNext : ι -> Bool
  next' (i : ι) : (hasNext i) -> ι
  cur' (i : ι) : (hasNext i) -> elem

variable {α : Type} {ι : Type} {elem : Type} {idx : Type}
variable [DecidableEq idx] [DecidableEq elem] [Iterator ι elem idx]

instance : Inhabited (Parse ι α) where
  default := fun it => Parser.Result.err it (.other "")

@[always_inline, inline]
protected def pure (a : α) : Parse ι α := fun it =>
  .ok it a

@[always_inline, inline]
protected def bind {α β : Type} (f : Parse ι α) (g : α -> Parse ι β) : Parse ι β := fun it =>
  match f it with
  | .ok pos res => g res pos
  | .err pos err => .err pos err

@[always_inline, inline]
def fail (s : String) : Parse ι α := fun it =>
  .err it (.other s)

@[inline]
def tryCatch (p : Parse ι α) (succ : α -> Parse ι β) (err : Unit -> Parse ι β)
  : Parse ι β := fun it =>
  match p it with
  | .ok pos res => succ res pos
  | .err rem e =>
    if Iterator.pos it = Iterator.pos rem then err () rem else .err rem e

@[always_inline]
instance : Monad (Parse ι) where
  pure := Parser.pure
  bind := Parser.bind

@[always_inline, inline]
def orElse (p : Parse ι α) (q : Unit -> Parse ι α) : Parse ι α :=
  tryCatch p pure q

@[always_inline, inline]
def attempt (p : Parse ι α) : Parse ι α := fun it =>
  match p it with
  | .ok rem res => .ok rem res
  | .err _ e => .err it e

/-- Replace a parser's internal error while preserving the failure position. -/
@[inline]
def label (p : Parse ι α) (message : String) : Parse ι α := fun it =>
  match p it with
  | .ok rem res => .ok rem res
  | .err rem _ => .err rem (.other message)

/--
  Inspect input without consuming it, on either success or failure.
  Failure also rewinds its reported position; use this for prediction, not committed diagnostics.
-/
@[inline]
def lookAhead (p : Parse ι α) : Parse ι α := fun it =>
  match p it with
  | .ok _ a => .ok it a
  | .err _ e => .err it e

@[always_inline]
instance : Alternative (Parse ι) where
  failure := fail ""
  orElse := orElse

@[inline]
def eof : Parse ι Unit := fun it =>
  if Iterator.hasNext it then
    .err it (.other "expected end of input")
  else
    .ok it ()

@[inline]
def isEof : Parse ι Bool := fun it =>
  .ok it (!Iterator.hasNext it)

/- desugaring for Lean4 Parsec implementation -/

@[specialize]
partial def manyCore (p : Parse ι α) (acc : Array α) : Parse ι <| Array α :=
  tryCatch p
    (fun x => manyCore p (acc.push x))
    (fun _ => pure acc)

@[inline]
def many (p : Parse ι α) : Parse ι (Array α) :=
  manyCore p #[]

@[inline]
def any : Parse ι elem := fun it =>
  if h : Iterator.hasNext it then
    let c := Iterator.cur' it h
    let it' := Iterator.next' it h
    .ok it' c
  else
    .err it (.other "expected any element")

@[inline]
def satisfy (pred : elem -> Bool) : Parse ι elem := attempt do
  let c <- any
  if pred c then return c else fail "satisfy: predicate not satisfied"

@[inline]
def peek? : Parse ι (Option elem) := fun it =>
  if h : Iterator.hasNext it then
    .ok it (some <| Iterator.cur' it h)
  else
    .ok it none

@[inline]
def peek! : Parse ι elem := fun it =>
  if h : Iterator.hasNext it then
    .ok it (Iterator.cur' it h)
  else
    .err it .eof

@[inline]
def skip : Parse ι Unit := fun it =>
  if h : Iterator.hasNext it then
    .ok (Iterator.next' it h) ()
  else
    .err it (.other "skip: expected element to skip")

end Parser
