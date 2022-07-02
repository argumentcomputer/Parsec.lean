import Parsec.Utils
import Parsec.Basic

namespace Parsec.String

namespace Parser

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

end Parser

/-
A function which converts an iterator to a ParseResult
-/
abbrev Parser (α : Type) : Type := Parsec.ParsecM String Parser.State α

namespace Parser

open ParseResult ParserState

/-
Get the iterator position.
-/
@[inline]
def getPos : Parser String.Pos := do
  let s ← get
  return s.it.pos

@[inline]
def fail (msg : String) : Parser α := fun pos =>
  error pos msg

@[inline]
def never : Parser Unit := fun pos => error pos ""

def getLineInfo : Parser (Nat × Nat) := λ pos => success pos (pos.line, pos.lineOffset)

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parser Unit := fun pos =>
  if pos.it.hasNext then
    error pos expectedEndOfInput
  else
    success pos ()

@[inline]
partial def manyCharsCore (p : Parser Char) (acc : String) : Parser String := do
  if let some res ← option p then
    manyCharsCore p (acc.push $ res)
  else
    pure acc

/-
Zero or more matching chars
-/
@[inline]
def manyChars (p : Parser Char) : Parser String := manyCharsCore p ""

/-
One or more matching chars
-/
@[inline]
def many1Chars (p : Parser Char) : Parser String := do manyCharsCore p (←p).toString

@[inline]
partial def manyStringsCore (p : Parser String) (acc : String) : Parser String :=
  (do manyStringsCore p (acc.append $ ←p))
  <|> pure acc

/-
One or more matching chars
-/
@[inline]
def many1Strings (p : Parser String) : Parser String := do
  manyStringsCore p (←p)

/-
Zero or more matching Strings
-/
@[inline]
def manyStrings (p : Parser String) : Parser String := manyStringsCore p ""

def pstring (s : String) : Parser String := λ pos =>
  let substr := pos.it.extract (pos.it.forward s.length)
  if substr = s then
    let it := pos.it.forward s.length
    success ({pos with it}) substr
  else
    error pos s!"expected: {s}"

@[inline]
def skipString (s : String) : Parser Unit := pstring s *> pure ()

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def anyChar : Parser Char := λ pos =>
  if pos.it.hasNext then
    success (nextStateIt pos) pos.it.curr
  else
    error pos unexpectedEndOfInput

/--
One of the given Chars
-/
@[inline]
def oneOfC (cs : List Char) : Parser Char := do
  let c ← anyChar
  if cs.contains c then
    pure c
  else
    fail s!"expected one of: {cs}"

@[inline]
def pchar (c : Char) : Parser Char := attempt do
  if (←anyChar) = c then pure c else fail s!"expected: '{c}'"

@[inline]
def oneOf (cs : List Char) : Parser Char := do
  let c ← anyChar
  if cs.contains c then
    pure c
  else
    fail s!"expected one of: {cs}"

@[inline]
def skipChar (c : Char) : Parser Unit := pchar c *> pure ()

@[inline]
def digit : Parser Char := attempt do
  let c ← anyChar
  if '0' ≤ c ∧ c ≤ '9' then pure c else fail s!"digit expected"

@[inline]
def hexDigit : Parser Char := attempt do
  let c ← anyChar
  if ('0' ≤ c ∧ c ≤ '9')
   ∨ ('a' ≤ c ∧ c ≤ 'a')
   ∨ ('A' ≤ c ∧ c ≤ 'A') then pure c else fail s!"hex digit expected"

@[inline]
def asciiLetter : Parser Char := attempt do
  let c ← anyChar
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then pure c else fail s!"ASCII letter expected"

@[inline]
def symbol : Parser String := attempt do
  let c ← asciiLetter
  let rest ← manyChars (asciiLetter <|> digit)
  return s!"{c}{rest}"


@[inline]
def satisfy (p : Char → Bool) (msg : String := "condition not satisfied") : Parser Char := attempt do
  let c ← anyChar
  if p c then pure c else fail msg

@[inline]
def notFollowedBy (p : Parser α) : Parser Unit := λ pos =>
  match p pos with
  | success _ _ => error pos "unexpected symbol"
  | error _ _ => success pos ()

@[inline]
def isWhitespace (c : Char) : Bool :=
  c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020'

/-
Non strict whitespace
-/
partial def skipWs : Parser Unit := λ pos =>
  let c := pos.it.curr
  if pos.it.hasNext && isWhitespace c then
    skipWs <| nextStateIt pos
  else
    success pos ()

@[inline]
def peek? : Parser (Option Char) := fun pos =>
  if pos.it.hasNext then
    success (nextStateIt pos) pos.it.curr
  else
    success pos none

@[inline]
def peek! : Parser Char := do
  let some c ← peek? | fail unexpectedEndOfInput
  pure c

@[inline]
def skip : Parser Unit := fun pos =>
  success pos ()

/-
Zero or more whitespaces
-/
@[inline]
def ws : Parser Unit := skipWs

/-
One or more whitespaces
-/
def wsStrict : Parser Unit := do
  _ ← satisfy isWhitespace
  ws

def parse {A: Type} (p: Parser A) (s : String) : Except String A :=
  match p { it := s.mkIterator : Parser.State } with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error pos err  =>
  let line := (s.split (λ c => c = '\n')).getD (pos.line-1) ""
  let pointer := "-".duplicate (pos.lineOffset-1) ++ "^"
  Except.error s!"\n{line}\n{pointer}\n{err} ({pos.line}:{pos.lineOffset})"

end Parser

end Parsec.String
