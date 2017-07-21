
data ABC = A | B | C

B_equals_B_is_B_equals_B : (B = B) = (B = B)
B_equals_B_is_B_equals_B = ?Refl

EqualsTypeOf : {t : Type} -> (x : t) -> Type
EqualsTypeOf x = x = x

refl_for_value : {t : Type} -> (x : t) -> EqualsTypeOf x
refl_for_value x = Refl

equals_equals_proof_for : {t : Type} -> (x : t) -> ((x = x) = (x = x))
equals_equals_proof_for x = refl_for_value (x = x)

B_equals_B_is_B_equals_B2 : (B = B) = (B = B)
B_equals_B_is_B_equals_B2 = equals_equals_proof_for B

{-B_equals_C_is_B_equals_C : (B = C) = (B = C)
B_equals_C_is_B_equals_C = Refl

B_equals_C_is_B_equals_B : (B = C) = (B = B)
B_equals_C_is_B_equals_B = Refl
-}
