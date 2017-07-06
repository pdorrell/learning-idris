import Data.Fin
import Data.Vect

%default total

data ABCD = A | B | C | D

abcd2Fin : ABCD -> Fin 4
abcd2Fin A = FZ
abcd2Fin B = (FS FZ)
abcd2Fin C = (FS (FS FZ))
abcd2Fin D = (FS (FS (FS FZ)))

interface FiniteType t where
  size : Nat
  values : Vect size t
  toFin : t -> Fin size
  fromFin : Fin size -> t
  toAndFromFin : (x : t) -> fromFin (toFin x) = x
  fromAndToFin : (y : Fin size) -> toFin (fromFin y) = y
  
FiniteType ABCD where
  size = 4
  values = [A, B, C, D]
  toFin = abcd2Fin
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
true_false_conflict {expr} expr_is_false expr_is_true = void $ trueNotFalse $ trans (sym expr_is_true) expr_is_false

eq_self_is_true : (x : ABCD) -> x == x = True
eq_self_is_true x = ?hole

x_is_y_implies_x_eq_y_is_true : (x : ABCD) -> (y : ABCD) -> x = y -> x == y = True
x_is_y_implies_x_eq_y_is_true x y x_is_y = rewrite (sym x_is_y) in eq_self_is_true x

eq_false_implies_not_equal : (x : ABCD) -> (y : ABCD) -> x == y = False -> x = y -> Void
eq_false_implies_not_equal x y x_eq_y_is_false x_is_y = 
  let x_eq_y_is_true = x_is_y_implies_x_eq_y_is_true x y x_is_y in
  true_false_conflict x_eq_y_is_false x_eq_y_is_true
  
eq_true_implies_equal : (x : ABCD) -> (y : ABCD) -> x == y = True -> x = y
eq_true_implies_equal A A x_eq_y_is_true = Refl
eq_true_implies_equal A B Refl impossible
eq_true_implies_equal A C Refl impossible
eq_true_implies_equal A D Refl impossible
eq_true_implies_equal B A Refl impossible
eq_true_implies_equal B B x_eq_y_is_true = Refl
eq_true_implies_equal B C Refl impossible
eq_true_implies_equal B D Refl impossible
eq_true_implies_equal C A Refl impossible
eq_true_implies_equal C B Refl impossible
eq_true_implies_equal C C x_eq_y_is_true = Refl
eq_true_implies_equal C D Refl impossible
eq_true_implies_equal D A Refl impossible
eq_true_implies_equal D B Refl impossible
eq_true_implies_equal D C Refl impossible
eq_true_implies_equal D D x_eq_y_is_true = Refl
