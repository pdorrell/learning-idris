%default total

is_sorted : {a: Type} -> (ltRel: a -> a -> Bool) -> List a -> Bool
is_sorted ltRel [] = True
is_sorted ltRel (x :: []) = True
is_sorted ltRel (x :: (y :: xs)) = 
  if ltRel x y then is_sorted ltRel (y :: xs) else False
  
example1 : is_sorted rel list_of_a = True -> something
example1 {rel} {list_of_a} list_of_a_is_sorted with (list_of_a)
  | [] = ? rhs1a
  | (x :: []) = ?rhs1b
  | (x :: y :: xs) with (rel x y)
    | True = ?rhs1c
    | False = ?rhs1d
    
data IsSorted : {a: Type} -> (ltRel: a -> a -> Type) -> List a -> Type where
  IsSortedZero : IsSorted {a=a} ltRel Nil
  IsSortedOne : (x: a) -> IsSorted ltRel [x]
  IsSortedMany : (x: a) -> (y: a) -> IsSorted rel (y::ys) -> (rel x y) -> IsSorted rel (x::y::ys)

example2 : IsSorted rel list_of_a -> something
example2 IsSortedZero = ?rhs2a
example2 (IsSortedOne x) = ?rhs2b
example2 (IsSortedMany x y z w) = ?rhs2c
