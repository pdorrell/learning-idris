is_sorted : {a: Type} -> (ltRel: a -> a -> Bool) -> List a -> Bool
is_sorted ltRel [] = True
is_sorted ltRel (x :: []) = True
is_sorted ltRel (x :: y :: xs) with (ltRel x y)
  | True = is_sorted ltRel (y :: xs)
  | False = False

is_sorted_true_elim : {x : a} -> is_sorted ltRel (x :: y :: xs) = True -> (ltRel x y = True, 
                                                                           is_sorted ltRel (y :: xs) = True)
is_sorted_true_elim {x} {y} {xs} {ltRel} is_sorted_x_y_xs = ?hole
