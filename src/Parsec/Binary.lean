import Parsec.Utils
import Parsec.Basic

namespace Parsec.Binary

namespace Parser

structure State where
  ref : ByteArray
  pos : Nat

instance : ParserState State where
  index s := s.pos
  next s := { s with pos := s.pos + 1 }

end Parser

abbrev Parser := ParsecM String Parser.State

namespace Parser

open ParseResult ParserState

@[inline]
def getPos : Parser Nat := do
  let s ← get
  return s.pos

@[inline]
def fail (msg : String) : Parser α := fun pos =>
  error pos msg

@[inline]
def never : Parser Unit := fun pos => error pos ""

@[inline]
def peek : Parser UInt8 := do
  let s ← get
  let ba := s.ref
  let pos := s.pos
  if h : pos < ba.size then
    pure <| ba.get ⟨pos, h⟩
  else
    fail "eof"

def read8 : Parser UInt8 :=
  peek <* modify fun s => { s with pos := s.pos + 1 }

def expectB (b : UInt8) : Parser Unit := do
  let b' ← read8
  unless b = b' do fail s!"got {b'}, expected {b}"

def expectBs (bs : ByteArray) : Parser Unit := do
  for b in bs do expectB b

def expectS (s : String) : Parser Unit := do
  expectBs s.toUTF8

def read16LE : Parser UInt16 := do
  let a ← read8
  let b ← read8
  return a.toUInt16 ||| (b.toUInt16 <<< 8)

def read16BE : Parser UInt16 := do
  let a ← read8
  let b ← read8
  return (a.toUInt16 <<< 8) ||| b.toUInt16

def read32LE : Parser UInt32 := do
  let a ← read8
  let b ← read8
  let c ← read8
  let d ← read8
  return a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24)

def read32BE : Parser UInt32 := do
  let a ← read8
  let b ← read8
  let c ← read8
  let d ← read8
  return (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32

def read64LE : Parser UInt64 := do
  return (← read32LE).toUInt64 ||| ((← read32LE).toUInt64 <<< 32)

def read64BE : Parser UInt64 := do
  return ((← read32BE).toUInt64 <<< 32) ||| (← read32BE).toUInt64

def readFloatBE : Parser Float :=
  read32BE <&> floatOf4Bytes

def readFloatLE : Parser Float :=
  read32LE <&> floatOf4Bytes

def readDoubleBE : Parser Float :=
  read64BE <&> floatOf8Bytes

def readDoubleLE : Parser Float :=
  read64LE <&> floatOf8Bytes

def readBytes (sz : Nat) : Parser ByteArray := do
  let s ← get
  let pos := s.pos
  let ba := s.ref
  if pos + sz <= ba.size then
    (pure <| ba.extract pos (pos + sz)) <* modify fun s => { s with pos := s.pos + sz }
  else
    fail s!"eof before {sz} bytes"

def readString (sz : Nat) : Parser String :=
  readBytes sz |>.map String.fromUTF8Unchecked

def readArray (n : Nat) (elem : Parser α) : Parser (Array α) := do
  let mut arr := #[]
  for _ in [0:n] do
    arr := arr.push (← elem)
  return arr

def remaining : Parser Nat := do
  let s ← get
  let pos := s.pos
  let ba := s.ref
  return ba.size - pos

def parse (p : Parser α) (ba : ByteArray) : Except String α := 
  match p { ref := ba, pos := 0 } with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error s err => Except.error s!"{s.pos}\n{err}"

end Parser
end Parsec.Binary
