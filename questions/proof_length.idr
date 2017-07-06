
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

eq_false_implies_not_equal A A x_eq_y_is_false _ = true_false_conflict (A == A) x_eq_y_is_false Refl
eq_false_implies_not_equal A B _ Refl impossible
eq_false_implies_not_equal A C _ Refl impossible
eq_false_implies_not_equal A D _ Refl impossible

eq_false_implies_not_equal B B x_eq_y_is_false _ = true_false_conflict (B == B) x_eq_y_is_false Refl
eq_false_implies_not_equal B A _ Refl impossible
eq_false_implies_not_equal B C _ Refl impossible
eq_false_implies_not_equal B D _ Refl impossible

eq_false_implies_not_equal C C x_eq_y_is_false _ = true_false_conflict (C == C) x_eq_y_is_false Refl
eq_false_implies_not_equal C A _ Refl impossible
eq_false_implies_not_equal C B _ Refl impossible
eq_false_implies_not_equal C D _ Refl impossible

eq_false_implies_not_equal D D x_eq_y_is_false _ = true_false_conflict (D == D) x_eq_y_is_false Refl
eq_false_implies_not_equal D A _ Refl impossible
eq_false_implies_not_equal D B _ Refl impossible
eq_false_implies_not_equal D C _ Refl impossible
