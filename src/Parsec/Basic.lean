namespace Parsec

universe u

/-!
## Abstract `ParsecM` Definition
-/

class ParserState (P : Type u) where
  /--
  Get the current parser index 
  -/
  index : P → Nat
  
  /--
  Move parser to the next symbol
  -/
  next : P → P

/-
Result which keeps track of the parsing state.
-/
inductive ParseResult (E S : Type u) [ParserState S] (α : Type u) where
  | success (state : S) (res : α)
  | error (state : S) (err : E)
  deriving Repr

open ParseResult ParserState

/-
Keep a record of parsers in use.
-/
class Backtrackable (δ : outParam (Type u)) (σ : Type u) where
  save    : σ → δ
  restore : σ → δ → σ

@[inline] def dummySave : σ → PUnit := fun _ => ⟨⟩

@[inline] def dummyRestore : σ → PUnit → σ := fun s _ => s

/- Dummy default instance -/
instance nonBacktrackable : Backtrackable PUnit σ where
  save    := dummySave
  restore := dummyRestore

def ParsecM (E S : Type u) [ParserState S] (α : Type u) : Type u := S → Parsec.ParseResult E S α

namespace ParsecM

variable {ε σ α β : Type u} [ParserState σ] [Inhabited ε]

instance [Inhabited ε] : Inhabited (ParsecM ε σ α) where
  default := fun s => error s default

@[inline] protected def pure (a : α) : ParsecM ε σ α := fun s =>
  success s a

@[inline] protected def set (s : σ) : ParsecM ε σ PUnit := fun _ =>
  success s PUnit.unit

@[inline] protected def get : ParsecM ε σ σ := fun s =>
  success s s

@[inline] protected def modifyGet (f : σ → Prod α σ) : ParsecM ε σ α := fun s =>
  match f s with
  | (a, s) => success s a

@[inline] protected def tryCatch {δ} [Backtrackable δ σ] {α} (x : ParsecM ε σ α) (handle : ε → ParsecM ε σ α) : ParsecM ε σ α := fun s =>
  let d := Backtrackable.save s
  match x s with
  | error s e => handle e (Backtrackable.restore s d)
  | success s a => success s a

/-
Combine two parsers into one where the first takes presedence
and the second is tried if the first one fails.
-/
@[inline]
def orElse {δ} [Backtrackable δ σ] (p : ParsecM ε σ α) (q : Unit → ParsecM ε σ α) : ParsecM ε σ α := fun s =>
  let d := Backtrackable.save s;
  let qres := q () (Backtrackable.restore s d);
  match p s with
  | error s err =>
    match qres with
    | error rem2 err2 =>
      -- Forward the error of the longest match
      if index s >= index rem2 then
        error s err
      else
        error rem2 err2
    | success rem a => success rem a
  | success s a  =>
    match qres with
    | error _rem2 _err2 => success s a
    | success rem2 a2 =>
      -- Forward the longest match
      if index s >= index rem2 then
        success s a
      else
        success rem2 a2

@[inline] protected def throw (e : ε) : ParsecM ε σ α := fun s =>
  error s e

@[inline] def adaptExcept {ε' : Type u} (f : ε → ε') (x : ParsecM ε σ α) : ParsecM ε' σ α := fun s =>
  match x s with
  | error s e => error s (f e)
  | success s a    => success s a

@[inline] protected def bind (x : ParsecM ε σ α) (f : α → ParsecM ε σ β) : ParsecM ε σ β := fun s =>
  match x s with
  | success s a => f a s
  | error s e => error s e

@[inline] protected def map (f : α → β) (x : ParsecM ε σ α) : ParsecM ε σ β := fun s =>
  match x s with
  | success s a => success s (f a) 
  | error s e => error s e

@[inline] protected def seqRight (x : ParsecM ε σ α) (y : Unit → ParsecM ε σ β) : ParsecM ε σ β := fun s =>
  match x s with
  | success s _ => y () s
  | error e s  => error e s

instance [ParserState σ] : Monad (ParsecM ε σ) where
  bind     := ParsecM.bind
  pure     := ParsecM.pure
  map      := ParsecM.map
  seqRight := ParsecM.seqRight

instance {δ} [Backtrackable δ σ] : OrElse (ParsecM ε σ α) where
  orElse := ParsecM.orElse
  
instance [ParserState σ] : MonadState σ (ParsecM ε σ) where
  set       := ParsecM.set
  get       := ParsecM.get
  modifyGet := ParsecM.modifyGet

instance {δ} [Backtrackable δ σ] : MonadExceptOf ε (ParsecM ε σ) where
  throw    := ParsecM.throw
  tryCatch := ParsecM.tryCatch

/--
Append two appendable parse results.
-/
@[inline]
def andAppend {α : Type u} [Append α] (f : ParsecM ε σ α) (g : ParsecM ε σ α) : ParsecM ε σ α := do 
  let a ← f
  let b ← g
  return a ++ b

/--
Append two heterogeneous appendable parse results.
-/
@[inline]
def andHAppend {A B C : Type u} [HAppend A B C] (f : ParsecM ε σ A) (g : ParsecM ε σ B) : ParsecM ε σ C := do 
  let a ← f
  let b ← g
  return a ++ b

instance {α : Type u} [Append α] : Append $ ParsecM ε σ α := ⟨andAppend ⟩

instance {A B C : Type u} [HAppend A B C] : HAppend (ParsecM ε σ A) (ParsecM ε σ B) (ParsecM ε σ C) :=
  ⟨andHAppend ⟩

instance [Backtrackable δ σ] : Alternative <| ParsecM ε σ :=
{ failure := ParsecM.throw default, orElse := ParsecM.orElse }

end ParsecM

/-!
## Common Combinators
-/

/-
Convert errors to none
-/
def option [ParserState σ] (p : ParsecM ε σ α) : ParsecM ε σ $ Option α := fun pos =>
  match p pos with
  | success rem a => success rem (some a)
  | error _rem _err => success pos (none)

/-
Try to match but rewind iterator if failure and return success bool
-/
def test [ParserState σ] (p : ParsecM ε σ α) : ParsecM ε σ Bool := fun pos =>
  match p pos with
  | success rem _a => success rem true
  | error _rem _err => success pos false

/-
Rewind the state on failure
-/
@[inline]
def attempt [ParserState σ] (p : ParsecM ε σ α) : ParsecM ε σ α := λ pos =>
  match p pos with
  | success rem res => success rem res
  | error _ err => error pos err


@[inline]
partial def manyCore  [ParserState σ] (p : ParsecM ε σ α) (acc : Array α) :  ParsecM ε σ $ Array α := do
  if let some res ← option p then
    manyCore p (acc.push $ res)
  else
    pure acc

@[inline]
def many [ParserState σ] (p : ParsecM ε σ α) : ParsecM ε σ $ Array α := manyCore p #[]

@[inline]
def many1 [ParserState σ] (p : ParsecM ε σ α) : ParsecM ε σ $ Array α := do manyCore p #[←p]



end Parsec
