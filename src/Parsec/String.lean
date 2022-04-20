import Parsec.Utils
import Parsec.State

namespace Parsec

structure State where
  it : String.Iterator
  line : Nat := 1
  lineOffset : Nat := 0
  deriving Repr, BEq

def isNewline (c : Char) : Bool :=
  c = '\n'

def nextStateIt (state : State) : State :=
  if isNewline state.it.curr then
    {state with it := state.it.next, lineOffset := 0, line := state.line + 1 }
  else
    {state with it := state.it.next, lineOffset := state.lineOffset + 1 }
  
instance : ParserState State where
  index state := state.it.i.byteIdx
  next := nextStateIt

end Parsec

/-
A function which converts an iterator to a ParseResult
-/
abbrev Parsec (α : Type) : Type := Parsec.ParsecM String Parsec.State α

namespace Parsec

open ParseResult ParserState

-- instance (α : Type) : Inhabited (Parsec α) :=
--   ⟨λ state => error state ""⟩

-- @[inline]
-- protected def pure (a : α) : Parsec α := λ state =>
--  success state a

-- @[inline]
-- def bind {α β : Type} (f : Parsec α) (g : α → Parsec β) : Parsec β := λ state =>
--   match f state with
--   | success rem a => g a rem
--   | error state msg => error state msg

-- instance : Monad Parsec :=
--   { pure := Parsec.pure, bind }

-- @[inline]
-- def map {α β : Type} (f : α → β) (p : Parsec α) : Parsec β := p >>= pure ∘ f


/-
Get the iterator position.
-/
@[inline]
def getPos : Parsec String.Pos := do
  let s ← get
  return s.it.pos

@[inline]
def andAppend {α : Type} [Append α] (f : Parsec α) (g : Parsec α) : Parsec α := do 
  let a ← f
  let b ← g
  return a ++ b

@[inline]
def andHAppend {A B C : Type} [HAppend A B C] (f : Parsec A) (g : Parsec B) : Parsec C := do 
  let a ← f
  let b ← g
  return a ++ b

instance {α : Type} [Append α] : Append $ Parsec α := ⟨andAppend⟩
instance {A B C : Type} [HAppend A B C] : HAppend (Parsec A) (Parsec B) (Parsec C) := ⟨andHAppend⟩

@[inline]
def fail (msg : String) : Parsec α := fun pos =>
  error pos msg

@[inline]
def never : Parsec Unit := fun pos => error pos ""

/-
Combine two parsers into one where the first takes presedence
and the second is tried if the first one fails.
-/
@[inline]
def orElse (p : Parsec α) (q : Unit → Parsec α) : Parsec α := fun pos =>
  let qres := q () pos
  match p pos with
  | success rem a =>
    match qres with
    | error rem2 err2 => success rem a
    | success rem2 a2 =>
      -- Forward the longest match
      if index rem >= index rem2 then
        success rem a
      else
        success rem2 a2
  | error rem err => 
    match qres with
    | error rem2 err2 =>
      -- Forward the error of the longest match
      if index rem >= index rem2 then
        error rem err
      else
        error rem2 err2
    | success rem a => success rem a

def getState : Parsec (Nat × Nat) := λ pos => success pos (pos.line, pos.lineOffset)

/-
Convert errors to none
-/
def option (p : Parsec α) : Parsec $ Option α := fun pos =>
  match p pos with
  | success rem a => success rem (some a)
  | error rem err => success pos (none)

/-
Try to match but rewind iterator if failure and return success bool
-/
def test (p : Parsec α) : Parsec Bool := fun pos =>
  match p pos with
  | success rem a => success rem true
  | error rem err => success pos false

/-
Rewind the state on failure
-/
@[inline]
def attempt (p : Parsec α) : Parsec α := λ pos =>
  match p pos with
  | success rem res => success rem res
  | error _ err => error pos err

instance : Alternative Parsec :=
{ failure := fail "", orElse }

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parsec Unit := fun pos =>
  if pos.it.hasNext then
    error pos expectedEndOfInput
  else
    success pos ()

@[inline]
partial def manyCore (p : Parsec α) (acc : Array α) : Parsec $ Array α := do
  if let some res ← option p then
    manyCore p (acc.push $ res)
  else
    pure acc

@[inline]
def many (p : Parsec α) : Parsec $ Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec α) : Parsec $ Array α := do manyCore p #[←p]

@[inline]
partial def manyCharsCore (p : Parsec Char) (acc : String) : Parsec String := do
  if let some res ← option p then
    manyCharsCore p (acc.push $ res)
  else
    pure acc

/-
Zero or more matching chars
-/
@[inline]
def manyChars (p : Parsec Char) : Parsec String := manyCharsCore p ""

/-
One or more matching chars
-/
@[inline]
def many1Chars (p : Parsec Char) : Parsec String := do manyCharsCore p (←p).toString

@[inline]
partial def manyStringsCore (p : Parsec String) (acc : String) : Parsec String :=
  (do manyStringsCore p (acc.append $ ←p))
  <|> pure acc

/-
One or more matching chars
-/
@[inline]
def many1Strings (p : Parsec String) : Parsec String := do
  manyStringsCore p (←p)

/-
Zero or more matching Strings
-/
@[inline]
def manyStrings (p : Parsec String) : Parsec String := manyStringsCore p ""

def pstring (s : String) : Parsec String := λ pos =>
  let substr := pos.it.extract (pos.it.forward s.length)
  if substr = s then
    let it := pos.it.forward s.length
    success ({pos with it}) substr
  else
    error pos s!"expected: {s}"

@[inline]
def skipString (s : String) : Parsec Unit := pstring s *> pure ()

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def anyChar : Parsec Char := λ pos =>
  if pos.it.hasNext then
    success (nextStateIt pos) pos.it.curr
  else
    error pos unexpectedEndOfInput

/--
One of the given Chars
-/
@[inline]
def oneOfC (cs : List Char) : Parsec Char := do
  let c ← anyChar
  if cs.contains c then
    pure c
  else
    fail s!"expected one of: {cs}"

@[inline]
def pchar (c : Char) : Parsec Char := attempt do
  if (←anyChar) = c then pure c else fail s!"expected: '{c}'"

@[inline]
def skipChar (c : Char) : Parsec Unit := pchar c *> pure ()

@[inline]
def digit : Parsec Char := attempt do
  let c ← anyChar
  if '0' ≤ c ∧ c ≤ '9' then pure c else fail s!"digit expected"

@[inline]
def hexDigit : Parsec Char := attempt do
  let c ← anyChar
  if ('0' ≤ c ∧ c ≤ '9')
   ∨ ('a' ≤ c ∧ c ≤ 'a')
   ∨ ('A' ≤ c ∧ c ≤ 'A') then pure c else fail s!"hex digit expected"

@[inline]
def asciiLetter : Parsec Char := attempt do
  let c ← anyChar
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then pure c else fail s!"ASCII letter expected"

@[inline]
def symbol : Parsec String := attempt do
  let c ← asciiLetter
  let rest ← manyChars (asciiLetter <|> digit)
  return s!"{c}{rest}"


@[inline]
def satisfy (p : Char → Bool) (msg : String := "condition not satisfied") : Parsec Char := attempt do
  let c ← anyChar
  if p c then pure c else fail msg

@[inline]
def notFollowedBy (p : Parsec α) : Parsec Unit := λ pos =>
  match p pos with
  | success _ _ => error pos "unexpected symbol"
  | error _ _ => success pos ()

@[inline]
def isWhitespace (c : Char) : Bool :=
  c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020'

/-
Non strict whitespace
-/
partial def skipWs : Parsec Unit := λ pos =>
  let c := pos.it.curr
  if pos.it.hasNext && isWhitespace c then
    skipWs <| nextStateIt pos
  else
    success pos ()

@[inline]
def peek? : Parsec (Option Char) := fun pos =>
  if pos.it.hasNext then
    success (nextStateIt pos) pos.it.curr
  else
    success pos none

@[inline]
def peek! : Parsec Char := do
  let some c ← peek? | fail unexpectedEndOfInput
  pure c

@[inline]
def skip : Parsec Unit := fun pos =>
  success pos ()

/-
Zero or more whitespaces
-/
@[inline]
def ws : Parsec Unit := skipWs

/-
One or more whitespaces
-/
def wsStrict : Parsec Unit := do
  _ ← satisfy isWhitespace
  ws

def parse {A: Type} (p: Parsec A) (s : String) : Except String A :=
  match p { it := s.mkIterator : Parsec.State } with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error pos err  =>
  let line := (s.split (λ c => c = '\n')).getD (pos.line-1) ""
  let pointer := "-".duplicate (pos.lineOffset-1) ++ "^"
  Except.error s!"\n{line}\n{pointer}\n{err} ({pos.line}:{pos.lineOffset})"

end Parsec
