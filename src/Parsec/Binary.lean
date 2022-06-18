import Parsec.Utils
import Parsec.State

namespace Parsec

structure ByteArrayParser.Error where
  pos : Nat
  msg : String
  deriving Repr, Inhabited

instance : ToString ByteArrayParser.Error where
  toString err := reprStr err

abbrev ByteArrayParser :=
  ReaderT ByteArray <| StateT Nat <| Except ByteArrayParser.Error

deriving instance Repr for Except

namespace ByteArrayParser

def parse (p : ByteArrayParser α) (b : ByteArray) (pos := 0) : Except ByteArrayParser.Error (α × Nat) :=
  (ReaderT.run p b).run pos

def parse' (p : ByteArrayParser α) (b : ByteArray) (pos := 0) : Except ByteArrayParser.Error α := do
  return (← p.run b pos).1

@[inline]
def error (msg : String) : ByteArrayParser α := do
  Except.error ({ pos := ← get, msg } : Error)

def peek : ByteArrayParser UInt8 := do
  let ba ← read
  let pos ← get
  if h : pos < ba.size then
    pure <| ba.get ⟨pos, h⟩
  else
    error "eof"

def read8 : ByteArrayParser UInt8 :=
  peek <* modify (· + 1)

def expectB (b : UInt8) : ByteArrayParser Unit := do
  let b' ← read8
  unless b = b' do error s!"got {b'}, expected {b}"

def expectBs (bs : ByteArray) : ByteArrayParser Unit := do
  for b in bs do expectB b

def read16LE : ByteArrayParser UInt16 := do
  let a ← read8
  let b ← read8
  return a.toUInt16 ||| (b.toUInt16 <<< 8)

def read32LE : ByteArrayParser UInt32 := do
  let a ← read8
  let b ← read8
  let c ← read8
  let d ← read8
  return a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24)

def read64LE : ByteArrayParser UInt64 := do
  return (← read32LE).toUInt64 ||| ((← read32LE).toUInt64 <<< 32)

def readBytes (sz : Nat) : ByteArrayParser ByteArray := do
  let pos ← get
  let ba ← read
  if pos + sz <= ba.size then
    (pure <| ba.extract pos (pos + sz)) <* modify (· + sz)
  else
    error s!"eof before {sz} bytes"

def readArray (n : Nat) (elem : ByteArrayParser α) : ByteArrayParser (Array α) := do
  let mut arr := #[]
  for _ in [0:n] do
    arr := arr.push (← elem)
  return arr

def remaining : ByteArrayParser Nat :=
  return (← read).size - (← get)
end ByteArrayParser
end Parsec
