%default total

PairedType : (t : Type) -> Type
PairedType t = (t, t)

NatPair : Type
NatPair = PairedType Nat

data WrappedNatPair : Type where
  MkWrappedNatPair : NatPair -> WrappedNatPair
  
equal_pair : t -> (t, t)
equal_pair x = (x, x)

Num WrappedNatPair where
  (MkWrappedNatPair (x1, x2)) + (MkWrappedNatPair (y1, y2)) = MkWrappedNatPair (x1 + y1, x2 + y2)
  (MkWrappedNatPair (x1, x2)) * (MkWrappedNatPair (y1, y2)) = MkWrappedNatPair (x1 * y1, x2 * y2)
  fromInteger x = MkWrappedNatPair $ equal_pair (fromInteger x)

WrappedNatPair_example : WrappedNatPair
WrappedNatPair_example = 4

BinaryOp : Type -> Type
BinaryOp t = t -> t -> t

lift_binary_op_to_pair : BinaryOp t -> BinaryOp (PairedType t)
lift_binary_op_to_pair op (x1, x2) (y1, y2) = (op x1 y1, op x2 y2)
  
[version2] Num WrappedNatPair where
  (MkWrappedNatPair x) + (MkWrappedNatPair y) = MkWrappedNatPair $ ((lift_binary_op_to_pair (+)) x y)
  (MkWrappedNatPair x) * (MkWrappedNatPair y) = MkWrappedNatPair $ ((lift_binary_op_to_pair (*)) x y)
  fromInteger x = MkWrappedNatPair $ equal_pair (fromInteger x)

interface Wrapper t where
  wrapped_type : Type
  wrap : wrapped_type -> t
  unwrap : t -> wrapped_type

Wrapper WrappedNatPair where
  wrapped_type = NatPair
  wrap x = MkWrappedNatPair x
  unwrap (MkWrappedNatPair x) = x

[version3] Num WrappedNatPair where
  x + y = ?h1
  x * y = ?h2
  fromInteger x = wrap $ equal_pair (the Nat (fromInteger x))
