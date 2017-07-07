import Data.Fin
import Data.Vect

%default total

data ABCD = A | B | C | D

interface FiniteType t where
  size : Nat
  values : Vect size t
  toFin : t -> Fin size
  fromFin : Fin size -> t
  toAndFromFin : (x : t) -> fromFin (toFin x) = x
  fromAndToFin : (y : Fin size) -> toFin (fromFin y) = y
  
FiniteType ABCD where
  size = the Nat 4
  values = [A, B, C, D]
  toFin A = FZ
  toFin B = (FS FZ)
  toFin C = (FS (FS FZ))
  toFin D = (FS (FS (FS FZ)))
  fromFin n = index n values
  toAndFromFin A = Refl
  toAndFromFin B = Refl
  toAndFromFin C = Refl
  toAndFromFin D = Refl
  fromAndToFin FZ = Refl
  fromAndToFin (FS FZ) = Refl
  fromAndToFin (FS (FS FZ)) = Refl
  fromAndToFin (FS (FS (FS FZ))) = Refl
  
Eq ABCD where
  x == y = toFin x == toFin y
  
true_false_conflict : {expr : Bool} -> expr = False -> expr = True -> Void
true_false_conflict {expr} expr_is_false expr_is_true = 
     void $ trueNotFalse $ trans (sym expr_is_true) expr_is_false

fin_eq_self_is_true : (n : Fin m) -> n == n = True
fin_eq_self_is_true FZ = Refl
fin_eq_self_is_true (FS x) = fin_eq_self_is_true x

eq_self_is_true : (x : ABCD) -> x == x = True
eq_self_is_true x = fin_eq_self_is_true $ toFin x

x_is_y_implies_x_eq_y_is_true : (x : ABCD) -> (y : ABCD) -> x = y -> x == y = True
x_is_y_implies_x_eq_y_is_true x y x_is_y = rewrite (sym x_is_y) in eq_self_is_true x

eq_false_implies_not_equal : (x : ABCD) -> (y : ABCD) -> x == y = False -> x = y -> Void
eq_false_implies_not_equal x y x_eq_y_is_false x_is_y = 
  let x_eq_y_is_true = x_is_y_implies_x_eq_y_is_true x y x_is_y in
  true_false_conflict x_eq_y_is_false x_eq_y_is_true
  
fin_eq_true_implies_equal : (x : Fin m) -> (y : Fin m) -> x == y = True -> x = y
fin_eq_true_implies_equal FZ FZ x_eq_y_is_true = Refl
fin_eq_true_implies_equal FZ (FS x) Refl impossible
fin_eq_true_implies_equal (FS x) FZ Refl impossible
fin_eq_true_implies_equal (FS x') (FS y') x_eq_y_is_true = 
  cong {f=FS} $ fin_eq_true_implies_equal x' y' $ the (x' == y' = True) x_eq_y_is_true

eq_true_implies_equal : (x : ABCD) -> (y : ABCD) -> x == y = True -> x = y
eq_true_implies_equal x y x_eq_y_is_true = 
  let lemma = fin_eq_true_implies_equal (toFin x) (toFin y) $ x_eq_y_is_true in 
  -- let lemma2 = cong {f=fromFin} lemma in
  ?eq_true_implies_equal_rhs
