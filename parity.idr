
data Parity = Even | Odd

opposite: Parity -> Parity
opposite Even = Odd
opposite Odd = Even

parityOf : Nat -> Parity
parityOf Z     = Even
parityOf (S x) = opposite $ parityOf x

data PNat : Parity -> Type where
     PZ : PNat Even
     PS : PNat p -> PNat $ opposite p
