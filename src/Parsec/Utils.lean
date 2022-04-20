namespace String

def duplicate (s : String) (n : Nat) : String :=
  match n with
  | 0 => s
  | Nat.succ ns => s ++ duplicate s ns

end String

namespace Parsec
instance : Repr ByteArray where
  reprPrec bs p := reprPrec bs.toList p

end Parsec
