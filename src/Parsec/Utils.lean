namespace String

/-- repeat `s` `n+1` times -/
def duplicate (s : String) (n : Nat) : String :=
  match n with
  | 0 => s
  | Nat.succ ns => s ++ duplicate s ns

end String

namespace Parsec

instance : Repr ByteArray where
  reprPrec bs p := reprPrec bs.toList p

deriving instance Repr for Except

@[extern c inline "((double)(*((float*)&#1)))"]
opaque floatOf4Bytes : UInt32 → Float

@[extern c inline "*((double*)&#1)"]
opaque floatOf8Bytes : UInt64 → Float

end Parsec
