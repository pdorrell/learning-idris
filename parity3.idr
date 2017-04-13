%default total

-- From Stackoverflow question

data Parity = Even | Odd

opposite: Parity -> Parity
opposite Even = Odd
opposite Odd  = Even

data PNat : Parity -> Type where
     PZ : PNat Even
     PS : PNat p -> PNat $ opposite p

nat2PNat : Nat -> (p ** PNat p)
nat2PNat Z    = (Even ** PZ)
nat2PNat (S x) with (nat2PNat x)
     | (p1 ** px) = (opposite(p1) ** (PS px))

nat2PNat_5 : nat2PNat 5 = (Odd ** PS (PS (PS (PS (PS PZ)))))
nat2PNat_5 = Refl

nat2PNat_S5 : nat2PNat (S 5) = (opposite (fst (nat2PNat 5)) ** (PS (snd (nat2PNat 5))))
nat2PNat_S5 = Refl

nat2PNat_Sn : (n : Nat) -> nat2PNat (S n) = (opposite (fst (nat2PNat n)) ** (PS (snd (nat2PNat n))))
nat2PNat_Sn Z     = Refl
nat2PNat_Sn (S k) with (nat2PNat k)
  nat2PNat_Sn (S k) | (p ** pn) = Refl



