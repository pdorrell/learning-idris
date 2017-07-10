%default total

data ABCD = A | B | C | D

abcd_choose : {t : Type} -> (a : t) -> (b : t) -> (c : t) -> (d : t) -> (x : ABCD) -> t
abcd_choose a b c d A = a
abcd_choose a b c d B = b
abcd_choose a b c d C = c
abcd_choose a b c d D = d

abcd_elim : {t : Type} -> (x : ABCD) -> (x = A -> t) -> (x = B -> t) -> (x = C -> t) -> (x = D -> t) -> t
abcd_elim {t} A from_a from_b from_c from_d = from_a Refl
abcd_elim {t} B from_a from_b from_c from_d = from_b Refl 
abcd_elim {t} C from_a from_b from_c from_d = from_c Refl
abcd_elim {t} D from_a from_b from_c from_d = from_d Refl
