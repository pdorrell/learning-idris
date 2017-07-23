
data ABC = A | B | C

refl_for_value : {t : Type} -> (x : t) -> x = x
refl_for_value x = Refl

B_equals_B_is_B_equals_B : (B = B) = (B = B)
B_equals_B_is_B_equals_B = refl_for_value (B = B)
