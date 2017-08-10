%default total

PairedType : (t : Type) -> Type
PairedType t = (t, t)

NatPair : Type
NatPair = PairedType Nat

data WrappedNatPair : Type where
  MkWrappedNatPair : NatPair -> WrappedNatPair
  
Num WrappedNatPair where
  (MkWrappedNatPair (x1, x2)) + (MkWrappedNatPair (y1, y2)) = MkWrappedNatPair (x1 + y1, x2 + y2)
  (MkWrappedNatPair (x1, x2)) * (MkWrappedNatPair (y1, y2)) = MkWrappedNatPair (x1 * y1, x2 * y2)
  fromInteger x = MkWrappedNatPair (nat_x, nat_x) where
    nat_x : Nat
    nat_x = fromInteger x

WrappedNatPair_example : WrappedNatPair
WrappedNatPair_example = 4

interface Wrapper t where
  wrapped_type : Type
  wrap : wrapped_type -> t
  unwrap : t -> wrapped_type

Wrapper WrappedNatPair where
  wrapped_type = NatPair
  wrap x = MkWrappedNatPair x
  unwrap (MkWrappedNatPair x) = x
