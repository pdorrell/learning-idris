infixl 4 &

(&) : Bool -> Bool -> Bool
(&) True True = True
(&) _ _ = False

elim_and : x & y = True -> (x = True, y = True)
elim_and {x = False} {y = False} x_and_y_is_true = (x_and_y_is_true, x_and_y_is_true)
elim_and {x = False} {y = True} x_and_y_is_true = (x_and_y_is_true, Refl)
elim_and {x = True} {y = False} x_and_y_is_true = (Refl, x_and_y_is_true)
elim_and {x = True} {y = True} x_and_y_is_true = (Refl, Refl)

is_sorted : {a: Type} -> (ltRel: a -> a -> Bool) -> List a -> Bool
is_sorted ltRel [] = True
is_sorted ltRel (x :: []) = True
is_sorted ltRel (x :: y :: xs) = (ltRel x y) & (is_sorted ltRel (y :: xs))

is_sorted_true_elim : {x : a} -> is_sorted ltRel (x :: y :: xs) = True -> (ltRel x y = True, 
                                                                           is_sorted ltRel (y :: xs) = True)
is_sorted_true_elim {x} {y} {xs} {ltRel} is_sorted_x_y_xs = 
  let lemma = the (is_sorted ltRel (x :: y :: xs) = (ltRel x y) & (is_sorted ltRel (y :: xs))) Refl in
    elim_and {x=ltRel x y} $ trans (sym lemma) is_sorted_x_y_xs

