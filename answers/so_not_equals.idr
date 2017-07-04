import Data.So

is_reflexive : (t -> t -> Bool) -> Type
is_reflexive {t} rel = (x : t) -> rel x x = True

is_symmetric : (t -> t -> Bool) -> Type
is_symmetric {t} rel = (x : t) -> (y : t) -> rel x y = rel y x

is_transitive : (t -> t -> Bool) -> Type
is_transitive {t} rel = (x : t) -> (y : t) -> (z : t) -> rel x y = True -> rel x z = rel y z

interface Eq t => LawfulEq t where
  eq_is_reflexive : is_reflexive {t} (==)
  eq_is_symmetric : is_symmetric {t} (==)
  eq_is_transitive : is_transitive {t} (==)

so_false_is_void : So False -> Void
so_false_is_void Oh impossible

so_not_y_eq_y_is_void : (y : Bool) -> So (not (y == y)) -> Void
so_not_y_eq_y_is_void False = so_false_is_void
so_not_y_eq_y_is_void True = so_false_is_void

data Weird = W

Eq Weird where
  W == W = False
  
weird_so_not_y_eq_y : (y : Weird) -> So (not (y == y))
weird_so_not_y_eq_y W = Oh

weird_eq_not_reflexive : is_reflexive {t=Weird} (==) -> Void
weird_eq_not_reflexive is_reflexive_eq = 
  let w_eq_w_is_true = is_reflexive_eq W in
    trueNotFalse $ trans (sym w_eq_w_is_true) (the (W == W = False) Refl)
