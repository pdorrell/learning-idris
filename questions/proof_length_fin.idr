import Data.Fin
import Data.Vect

%default total

-- the FiniteType interface, representing a type with a finite number of possible values

interface FiniteType t where
  size : Nat
  values : Vect size t
  toFin : t -> Fin size
  fromFin : Fin size -> t
  toAndFromFin : (x : t) -> the t (fromFin (toFin x)) = x
  fromAndToFin : (y : Fin size) -> toFin (fromFin y) = y
  
  fromFin n = index n values
  
toFin_injective : FiniteType t => (x : t) -> (y : t) -> toFin x = toFin y -> x = y
toFin_injective {t} x y tofin_x_is_tofin_y = 
  let x_to_and_from_fin_is_y_to_and_from_fin = cong {f=fromFin} tofin_x_is_tofin_y in
    trans (trans (sym $ toAndFromFin x) x_to_and_from_fin_is_y_to_and_from_fin) (toAndFromFin y)
    
eq_from_fin : FiniteType t => t -> t -> Bool
eq_from_fin x y = toFin x == toFin y

fin_eq_reflexive : (x : Fin n) -> x == x = True
fin_eq_reflexive FZ = Refl
fin_eq_reflexive (FS x) = fin_eq_reflexive x

eq_from_fin_reflexive : FiniteType t => (x : t) -> eq_from_fin x x = True
eq_from_fin_reflexive x = fin_eq_reflexive $ toFin x

-- lemmas

fin_eq_true_implies_equal : (x : Fin m) -> (y : Fin m) -> x == y = True -> x = y
fin_eq_true_implies_equal FZ FZ x_eq_y_is_true = Refl
fin_eq_true_implies_equal FZ (FS x) Refl impossible
fin_eq_true_implies_equal (FS x) FZ Refl impossible
fin_eq_true_implies_equal (FS x') (FS y') x_eq_y_is_true = 
  cong {f=FS} $ fin_eq_true_implies_equal x' y' $ the (x' == y' = True) x_eq_y_is_true
  
true_false_conflict : {expr : Bool} -> expr = False -> expr = True -> Void
true_false_conflict {expr} expr_is_false expr_is_true = 
     void $ trueNotFalse $ trans (sym expr_is_true) expr_is_false

fin_eq_self_is_true : (n : Fin m) -> n == n = True
fin_eq_self_is_true FZ = Refl
fin_eq_self_is_true (FS x) = fin_eq_self_is_true x

-- interface EqFromFinEq
  
interface (FiniteType t, Eq t) => EqFromFinEq t where
  eq_is_from_fin : (x : t) -> (y : t) -> x == y = eq_from_fin x y
  
eq_self_is_true : EqFromFinEq t => (x : t) -> x == x = True
eq_self_is_true x = trans (eq_is_from_fin x x) (eq_from_fin_reflexive x)
  
x_is_y_implies_x_eq_y_is_true : EqFromFinEq t => (x : t) -> (y : t) -> x = y -> x == y = True
x_is_y_implies_x_eq_y_is_true x y x_is_y = rewrite (sym x_is_y) in eq_self_is_true x

eq_false_implies_not_equal : EqFromFinEq t => (x : t) -> (y : t) -> x == y = False -> x = y -> Void
eq_false_implies_not_equal x y x_eq_y_is_false x_is_y = 
  let x_eq_y_is_true = x_is_y_implies_x_eq_y_is_true x y x_is_y in
  true_false_conflict x_eq_y_is_false x_eq_y_is_true
  
eq_true_implies_equal : EqFromFinEq t => (x : t) -> (y : t) -> x == y = True -> x = y
eq_true_implies_equal x y x_eq_y_is_true = 
  let eq_from_fin_x_y_is_true = trans (sym (eq_is_from_fin x y)) x_eq_y_is_true in
  let tofin_x_is_to_fin_y = fin_eq_true_implies_equal (toFin x) (toFin y) $ eq_from_fin_x_y_is_true in
    toFin_injective x y tofin_x_is_to_fin_y

-- ABCD example

data ABCD = A | B | C | D

FiniteType ABCD where
  size = the Nat 4
  values = [A, B, C, D]
  toFin A = FZ
  toFin B = (FS FZ)
  toFin C = (FS (FS FZ))
  toFin D = (FS (FS (FS FZ)))
  toAndFromFin A = Refl
  toAndFromFin B = Refl
  toAndFromFin C = Refl
  toAndFromFin D = Refl
  fromAndToFin FZ = Refl
  fromAndToFin (FS FZ) = Refl
  fromAndToFin (FS (FS FZ)) = Refl
  fromAndToFin (FS (FS (FS FZ))) = Refl
  
Eq ABCD where
  (==) = eq_from_fin
  
EqFromFinEq ABCD where
  eq_is_from_fin = \x, y => Refl
  
abcd_eq_self_is_true : (x : ABCD) -> x == x = True
abcd_eq_self_is_true = eq_self_is_true

abcd_eq_false_implies_not_equal : (x : ABCD) -> (y : ABCD) -> x == y = False -> x = y -> Void
abcd_eq_false_implies_not_equal = eq_false_implies_not_equal

abcd_eq_true_implies_equal : (x : ABCD) -> (y : ABCD) -> x == y = True -> x = y
abcd_eq_true_implies_equal = eq_true_implies_equal
