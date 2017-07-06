
data ABCD = A | B | C | D

Eq ABCD where
  A == A = True
  B == B = True
  C == C = True
  D == D = True
  _ == _ = False
  
true_false_conflict : (expr : Bool) -> expr = False -> expr = True -> Void
true_false_conflict expr expr_is_false expr_is_true = void $ trueNotFalse $ trans (sym expr_is_true) expr_is_false

eq_false_implies_not_equal : (x : ABCD) -> (y : ABCD) -> x == y = False -> x = y -> Void

eq_false_implies_not_equal x y x_eq_y_is_false x_is_y with (x == y) proof p
  eq_false_implies_not_equal x y x_eq_y_is_false x_is_y | True = true_false_conflict True x_eq_y_is_false Refl
  eq_false_implies_not_equal x y x_eq_y_is_false x_is_y | False = ?hole1

