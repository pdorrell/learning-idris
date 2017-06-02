%default total

is_inverse_of: Eq a => (a -> a) -> (a -> a) -> Type
is_inverse_of {a} f f' = (x : a) -> (f (f' x)) == x = True

are_inverses : Eq a => (a -> a) -> (a -> a) -> Type
are_inverses f f' = (is_inverse_of f f', is_inverse_of f' f)

data FunctionAndInverse : (a : Type) -> Type where
  FunAndInverse : Eq a => (f : a -> a) -> (f' : a -> a) -> (are_inverses f f') -> FunctionAndInverse a
  
interface BidirectionalRepeater t where
   repeat : t -> (a -> a, a -> a) -> a -> a
   
bi_repeat : BidirectionalRepeater t => t -> FunctionAndInverse a -> a -> a
bi_repeat r (FunAndInverse f f' y) x = repeat r (f, f') x

equal_bi_repeaters : (BidirectionalRepeater t1, BidirectionalRepeater  t2) => (r1 : t1) -> (r2 : t2) -> Type
equal_bi_repeaters r1 r2 = (a : Type) -> Eq a -> (fai : FunctionAndInverse a) -> (x : a) -> bi_repeat r1 fai x == bi_repeat r2 fai x = True
