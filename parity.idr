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

opposite_its_own_inverse : (p : Parity) -> p = opposite (opposite p)
opposite_its_own_inverse Even = Refl
opposite_its_own_inverse Odd  = Refl

fst_of_dpair: (p:Parity) -> PNat p -> fst (p**pn) = p
fst_of_dpair p x = Refl

parityOf_gets_parity_for5: parityOf 5 = fst (nat2PNat 5)
parityOf_gets_parity_for5 = Refl

opposite_is_mono : (p1,p2 : Parity) -> opposite p1 = opposite p2 -> p1 = p2
opposite_is_mono p1 p2 prf = rewrite opposite_its_own_inverse p1 in rewrite opposite_its_own_inverse p2 in cong { f = opposite } prf

nat2PNat_Sn : (n : Nat) -> nat2PNat (S n) = (opposite (fst (nat2PNat n)) ** (PS (snd (nat2PNat n))))
nat2PNat_Sn Z     = Refl
nat2PNat_Sn (S k) with (nat2PNat k)
  nat2PNat_Sn (S k) | (p ** pn) = Refl

parityOf_gets_parity_5 :  parityOf 5 = fst (nat2PNat 5)
parityOf_gets_parity_5 = Refl

parityOf_gets_parity : (n : Nat) -> parityOf n = fst (nat2PNat n)
parityOf_gets_parity Z     = Refl
parityOf_gets_parity (S k) with (nat2PNat k)
  parityOf_gets_parity (S k) | (p ** pn) = ?rhs_parity
