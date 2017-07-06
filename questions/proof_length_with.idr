%default total

data ABCD = A | B | C | D

Eq ABCD where
  A == A = True
  B == B = True
  C == C = True
  D == D = True
  _ == _ = False
  
true_false_conflict : (expr : Bool) -> expr = False -> expr = True -> Void
true_false_conflict expr expr_is_false expr_is_true = void $ trueNotFalse $ trans (sym expr_is_true) expr_is_false

eq_self_is_true : (x : ABCD) -> x == x = True
eq_self_is_true A = Refl
eq_self_is_true B = Refl
eq_self_is_true C = Refl
eq_self_is_true D = Refl

eq_self_false_implies_void : (x : ABCD) -> x == x = False -> Void
eq_self_false_implies_void x x_eq_x_is_false = true_false_conflict (x==x) x_eq_x_is_false (eq_self_is_true x) 

x_is_y_implies_x_eq_y_is_true : (x : ABCD) -> (y : ABCD) -> x = y -> x == y = True
x_is_y_implies_x_eq_y_is_true x y x_is_y = rewrite (sym x_is_y) in eq_self_is_true x

eq_false_implies_not_equal : (x : ABCD) -> (y : ABCD) -> x == y = False -> x = y -> Void
eq_false_implies_not_equal x y x_eq_y_is_false x_is_y = 
  let x_eq_y_is_true = x_is_y_implies_x_eq_y_is_true x y x_is_y in
  true_false_conflict (x == y) x_eq_y_is_false x_eq_y_is_true