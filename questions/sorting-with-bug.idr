%default total

interface Sortable t where
  total (<) : t -> t -> Bool

is_sorted : Sortable a => List a -> Bool
is_sorted [] = True
is_sorted (x :: []) = True
is_sorted (x :: (y :: xs)) with (x < y)
  | True = is_sorted (y :: xs)
  | False = False

data IsSorted : {a: Type} -> (ltRel: a -> a -> Type) -> List a -> Type where
  IsSortedZero : IsSorted {a=a} ltRel Nil
  IsSortedOne : (x: a) -> IsSorted ltRel [x]
  IsSortedMany : (x: a) -> (y: a) -> .IsSorted rel (y::ys) -> .(rel x y) -> IsSorted rel (x::y::ys)

example : IsSorted rel list_of_a -> something
example IsSortedZero = ?example_rhs_1
example (IsSortedOne x) = ?example_rhs_2
example (IsSortedMany x y z w) = ?example_rhs_3
