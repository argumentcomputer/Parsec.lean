namespace String

def duplicate (s : String) (n : Nat) : String :=
  match n with
  | 0 => s
  | Nat.succ ns => s ++ duplicate s ns

end String

namespace Parsec
instance : Repr ByteArray where
  reprPrec bs p := reprPrec bs.toList p

class ParserState (P : Type) where
  /--
  Get the current parser index 
  -/
  index : P → Nat
  
  /--
  Move parser to the next symbol
  -/
  next : P → P

end Parsec
