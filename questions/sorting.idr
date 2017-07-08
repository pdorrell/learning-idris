data IsSorted : {a: Type} -> (ltRel: a -> a -> Type) -> List a -> Type where
  IsSortedZero : IsSorted {a} ltRel Nil
  IsSortedOne : (x: a) -> IsSorted ltRel [x]
  IsSortedMany : (x: a) -> (y: a) -> IsSorted ltRel (y::ys) -> (ltRel x y) -> IsSorted ltRel (x::y::ys)

example : IsSorted ltRel list_of_a -> something
example IsSortedZero = ?rhs1
example (IsSortedOne x) = ?rhs2
example (IsSortedMany x y xs x_lt_y) = ?rhs3
