%default total

data ABCD = A | B | C | D

abcd_elim : {Prop : ABCD -> Type} -> (Prop A, Prop B, Prop C, Prop D) -> (x : ABCD) -> Prop x
abcd_elim {Prop} (prop_a, prop_b, prop_c, prop_d) A = prop_a
abcd_elim {Prop} (prop_a, prop_b, prop_c, prop_d) B = prop_b
abcd_elim {Prop} (prop_a, prop_b, prop_c, prop_d) C = prop_c
abcd_elim {Prop} (prop_a, prop_b, prop_c, prop_d) D = prop_d

nat_elim : {Prop : Nat -> Type} -> (Prop Z, ((n : Nat) -> Prop n -> Prop (S n))) -> (x : Nat) -> Prop x
nat_elim {Prop} (prop_z, prop_s) Z = prop_z
nat_elim {Prop} (prop_z, prop_s) (S k) = prop_s k $ nat_elim (prop_z, prop_s) k

-- a naive attempt to develop the concept of elimination as an interface ...

interface Eliminatable t where
  elim_premises_type : (Prop : t -> Type) -> Type
  elim : {Prop : t -> Type} -> elim_premises_type Prop -> (x : t) -> Prop x
  
Eliminatable ABCD where
  elim_premises_type Prop = (Prop A, Prop B, Prop C, Prop D)
  elim = abcd_elim

Eliminatable Nat where
  elim_premises_type Prop = (Prop Z, ((n : Nat) -> Prop n -> Prop (S n)))
  elim = nat_elim

-- but we can cheat and define the end goal as the premises type
[cheat] Eliminatable ABCD where
  elim_premises_type Prop = (x : ABCD) -> Prop x
  elim = id
