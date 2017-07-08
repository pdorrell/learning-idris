infixl 4 &

(&) : Bool -> Bool -> Bool
(&) True True = True
(&) _ _ = False

left_elim_and : x & y = True -> x = True
left_elim_and {x = False} {y} False_and_y_is_true = False_and_y_is_true
left_elim_and {x = True} {y} True_and_y_is_true = Refl


is_sorted : {a: Type} -> (ltRel: a -> a -> Bool) -> List a -> Bool
is_sorted ltRel [] = True
is_sorted ltRel (x :: []) = True
is_sorted ltRel (x :: y :: xs) = (ltRel x y) & (is_sorted ltRel (y :: xs))

unfold1 : {x : a} -> is_sorted rel (x :: y :: xs) = True -> rel x y = True
unfold1 {x} {y} {xs} {rel} is_sorted_x_y_xs = 
  let lemma = the (is_sorted rel (x :: y :: xs) = (rel x y) & (is_sorted rel (y :: xs))) Refl in
    left_elim_and {x=rel x y} $ trans (sym lemma) is_sorted_x_y_xs
