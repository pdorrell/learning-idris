
two_is_two : 2 ~=~ 2
two_is_two = Refl

two: Nat
two = S (S Z)

z_refl_is_z_refl : the (Z = Z) Refl = the (Z = Z) Refl
z_refl_is_z_refl = Refl

--z_refl_is_sz_refl : the (Z = Z) Refl = the (S Z = S Z) Refl
--z_refl_is_sz_refl = Refl

data ABC = A | B | C

b_equals_b : Type
b_equals_b = B = B

b_equals_b2 : Type
b_equals_b2 = B = B

b_equals_b_refl_is_b_equals_b2_refl : the Main.b_equals_b Refl = the Main.b_equals_b2 Refl
b_equals_b_refl_is_b_equals_b2_refl = Refl

equal_equality_types2 : Main.b_equals_b = Main.b_equals_b
equal_equality_types2 = ?hole

equality_equals_equality : Type
equality_equals_equality = Main.b_equals_b = Main.b_equals_b

equal_equality_types4 : Main.equality_equals_equality
equal_equality_types4 = ?hole


--equal_equality_types3 : Main.b_equals_b = Main.b_equals_b2
--equal_equality_types3 = ?hole

equal_equality_types : (B = B) = (B = B)
equal_equality_types = ?hole

{-
equal_nats : Nat = Nat
equal_nats = Refl

equal_list_nats : List Nat = List Nat
equal_list_nats = Refl

list_nat : Type
list_nat = List Nat

equal_list_nats2 : Main.list_nat = List Nat
equal_list_nats2 = Refl

-}
