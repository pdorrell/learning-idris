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

pNat2Nat : PNat p -> Nat
pNat2Nat PZ     = Z
pNat2Nat (PS x) = S (pNat2Nat x)

nat2PNat : Nat -> (p ** PNat p)
nat2PNat Z    = (Even ** PZ)
nat2PNat (S x) with (nat2PNat x)
     | (p1 ** px) = (opposite(p1) ** (PS px))
