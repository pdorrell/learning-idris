%default total

data ABCD = A | B | C | D

abcd_choose : {t : Type} -> (a : t) -> (b : t) -> (c : t) -> (d : t) -> (x : ABCD) -> t
abcd_choose a b c d A = a
abcd_choose a b c d B = b
abcd_choose a b c d C = c
abcd_choose a b c d D = d

abcd_elim_eql : {t : Type} -> (x : ABCD) -> (x = A -> t) -> (x = B -> t) -> (x = C -> t) -> (x = D -> t) -> t
abcd_elim_eql {t} A from_a from_b from_c from_d = from_a Refl
abcd_elim_eql {t} B from_a from_b from_c from_d = from_b Refl 
abcd_elim_eql {t} C from_a from_b from_c from_d = from_c Refl
abcd_elim_eql {t} D from_a from_b from_c from_d = from_d Refl

abcd_elim : (Prop : ABCD -> Type) -> Prop A -> Prop B -> Prop C -> Prop D -> (x : ABCD) -> Prop x
abcd_elim Prop prop_a prop_b prop_c prop_d A = prop_a
abcd_elim Prop prop_a prop_b prop_c prop_d B = prop_b
abcd_elim Prop prop_a prop_b prop_c prop_d C = prop_c
abcd_elim Prop prop_a prop_b prop_c prop_d D = prop_d

nat_elim : (Prop : Nat -> Type) -> Prop Z -> ((n : Nat) -> Prop n -> Prop (S n)) -> (x : Nat) -> Prop x
nat_elim Prop prop_z prop_s Z = prop_z
nat_elim Prop prop_z prop_s (S k) = prop_s k $ nat_elim Prop prop_z prop_s k
