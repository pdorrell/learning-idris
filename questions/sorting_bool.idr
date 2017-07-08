is_sorted : {a: Type} -> (ltRel: a -> a -> Bool) -> List a -> Bool
is_sorted ltRel [] = True
is_sorted ltRel (x :: []) = True
is_sorted ltRel (x :: y :: xs) with (ltRel x y)
  | True = is_sorted ltRel (y :: xs)
  | False = False

unfold1 : {x : a} -> is_sorted rel (x :: y :: xs) = True -> rel x y = True
unfold1 {x} {y} {xs} {rel} is_sorted_x_y_xs with (rel x y) proof rel_x_y
  | True = Refl
  | False = 
    let lemma = the (is_sorted rel (x :: y :: xs) = False) Refl in
    ?rhs2
