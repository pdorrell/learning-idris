%default total

data Parity = Even | Odd

opposite: Parity -> Parity
opposite Even = Odd
opposite Odd  = Even

parityOf : Nat -> Parity
parityOf Z     = Even
parityOf (S x) = opposite $ parityOf x

data PNat : Parity -> Type where
     PZ : PNat Even
     PS : PNat p -> PNat $ opposite p
     
parityOfPNat: (pn: PNat p) -> Parity
parityOfPNat PZ = Even
parityOfPNat (PS pn) = opposite $ parityOfPNat pn

pNat2Nat : PNat p -> Nat
pNat2Nat PZ     = Z
pNat2Nat (PS x) = S (pNat2Nat x)

nat2PNat : Nat -> (p ** PNat p)
nat2PNat Z    = (Even ** PZ)
nat2PNat (S x) with (nat2PNat x)
     | (p1 ** px) = (opposite(p1) ** (PS px))
     
nat2PNat_5 : nat2PNat 5 = (Odd ** PS (PS (PS (PS (PS PZ)))))
nat2PNat_5 = Refl

opposite_its_own_inverse : (p : Parity) -> opposite (opposite p) = p
opposite_its_own_inverse Even = Refl
opposite_its_own_inverse Odd  = Refl

lemma: (n : Nat) -> opposite (parityOf n) = parityOf (S n)
lemma n = Refl

parityOf_gets_parity_for5: parityOf 5 = fst (nat2PNat 5)
parityOf_gets_parity_for5 = Refl

opposite_cong_eq : (p1,p2 : Parity) -> p1 = p2 -> opposite p1 = opposite p2
opposite_cong_eq p1 p2 prf = cong {f = opposite} prf

opposite_lemma : (p1,p2 : Parity) -> opposite p1 = opposite p2 -> opposite (opposite p1) = opposite (opposite p2)
opposite_lemma p1 p2 prf = cong {f = opposite} prf

opposite_is_mono : (p1,p2 : Parity) -> opposite p1 = opposite p2 -> p1 = p2 
opposite_is_mono p1 p2 prf = rewrite sym (opposite_its_own_inverse p1) in rewrite sym (opposite_its_own_inverse p2) in opposite_lemma p1 p2 prf

parityOf_gets_parity_ind_hyp: (n : Nat) -> parityOf n = fst (nat2PNat n) -> parityOf (S n) = fst (nat2PNat (S n))
parityOf_gets_parity_ind_hyp n prf with (nat2PNat n)
  parityOf_gets_parity_ind_hyp n prf | (p ** pn) = ?rhs2

parityOf_gets_parity : (n : Nat) -> parityOf n = fst (nat2PNat n)
parityOf_gets_parity Z     = Refl
parityOf_gets_parity (S k) with (nat2PNat k)
  parityOf_gets_parity (S k) | (p ** pn) = ?rhs
