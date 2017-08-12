{-
Can I write a generic function-wrapping function for a Wrapper interface 
representing a type that wraps some other type?


The following is a simplified and slightly contrived example of my problem.

NatPair is a pair of Nats, and I want to "lift" Num operations to NatPair pointwise.
Which the function `lift_binary_op_to_pair` does.

But I can't implement `Num NatPair` because `NatPair` is not a data constructor.

So, I wrap it in a type WrappedNatPair.

Then I want to generalise the idea of a wrapper type, with my `Wrapper` interface.

The function `lift_natpair_bin_op_to_wrapped` can lift a binary operation from NatPair
to WrappedNatPair, and the implementation code is entirely in terms of the `unwrap` and
`wrap` `Wrapper` interface methods.

But, if I try to generalise to 

lift_bin_op_to_wrapped : Wrapper t => BinaryOp WrappedType -> BinaryOp t

then the type signature won't even compile, with error:

 `-- Wrapping.idr line 72 col 23:
     When checking type of Main.lift_bin_op_to_wrapped:
     Can't find implementation for Wrapper t

(where the error location is just where the ':' is).

-}

%default total

PairedType : (t : Type) -> Type
PairedType t = (t, t)

NatPair : Type
NatPair = PairedType Nat

data WrappedNatPair : Type where
  MkWrappedNatPair : NatPair -> WrappedNatPair
  
equal_pair : t -> PairedType t
equal_pair x = (x, x)

BinaryOp : Type -> Type
BinaryOp t = t -> t -> t

lift_binary_op_to_pair : BinaryOp t -> BinaryOp (PairedType t)
lift_binary_op_to_pair op (x1, x2) (y1, y2) = (op x1 y1, op x2 y2)
  
interface Wrapper t where
  WrappedType : Type
  wrap : WrappedType -> t
  unwrap : t -> WrappedType

Wrapper WrappedNatPair where
  WrappedType = NatPair
  wrap x = MkWrappedNatPair x
  unwrap (MkWrappedNatPair x) = x
  
lift_natpair_bin_op_to_wrapped : BinaryOp NatPair -> BinaryOp WrappedNatPair
lift_natpair_bin_op_to_wrapped op x y = 
    let unwrapped_x = unwrap x
        unwrapped_y = unwrap y
        in wrap $ op unwrapped_x unwrapped_y

Num WrappedNatPair where
  (+) = lift_natpair_bin_op_to_wrapped (lift_binary_op_to_pair (+))
  (*) = lift_natpair_bin_op_to_wrapped (lift_binary_op_to_pair (*))
  fromInteger x = wrap $ equal_pair (fromInteger x)

WrappedNatPair_example : the WrappedNatPair 8 = (the WrappedNatPair 2) + (the WrappedNatPair 6)
WrappedNatPair_example = Refl

-- The following won't compile:        
-- lift_bin_op_to_wrapped : Wrapper t => BinaryOp WrappedType -> BinaryOp t
