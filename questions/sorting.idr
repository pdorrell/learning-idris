data IsSorted : {a: Type} -> (ltRel: a -> a -> Type) -> List a -> Type where
  IsSortedZero : IsSorted {a=a} ltRel Nil
  IsSortedOne : (x: a) -> IsSorted ltRel [x]
  IsSortedMany : (x: a) -> (y: a) -> IsSorted rel (y::ys) -> (rel x y) -> IsSorted rel (x::y::ys)

example1 : IsSorted rel list_of_a -> something
example1 IsSortedZero = ?rhs3a
example1 (IsSortedOne x) = ?rhs3b
example1 (IsSortedMany x y z w) = ?rhs3c

