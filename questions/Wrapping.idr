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

I think the problem is that `t` doesn't appear anywhere in the
type signature for the `Wrapper` interface `WrapperType` method,
so `WrapperType` can't be invoked anywhere other than inside
the interface definition itself.
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
  
interface Wraps (from : Type) (to : Type) | to where
  wrap   : from -> to
  unwrap : to   -> from
  
-- from https://stackoverflow.com/questions/45646004

Wraps NatPair WrappedNatPair where
  wrap = MkWrappedNatPair
  unwrap (MkWrappedNatPair x) = x

lift_bin_op_to_wrapped : Wraps from to  => BinaryOp from -> BinaryOp to
lift_bin_op_to_wrapped op x y = wrap $ op (unwrap x) (unwrap y)

Num WrappedNatPair where
  (+) = lift_bin_op_to_wrapped (lift_binary_op_to_pair {t=Nat} (+))
  (*) = lift_bin_op_to_wrapped (lift_binary_op_to_pair {t=Nat} (*))
  fromInteger = wrap . equal_pair {t=Nat} . fromInteger
  
WrappedNatPair_example : the WrappedNatPair 8 = (the WrappedNatPair 2) + (the WrappedNatPair 6)
WrappedNatPair_example = Refl
