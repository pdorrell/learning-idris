module LawfulEquality

%default total

public export
interface Eq t => LawfulEq t where
  eq_is_reflexive : (x : t) -> x == x = True
  eq_is_symmetric : (x : t) -> (y : t) -> x == y = y == x
  eq_is_transitive : (x : t) -> (y : t) -> (z : t) -> x == y = True -> x == z = y == z
