%default total

{- In the Idris documentation there is a Parity example where Odd or Even belong
   to type Parity n for a natural number n depending on if it's even or odd.
   Here I explore doing it the other way round.
 -}
 
 -- This file is like parity.idr, but I avoid using a 'with' in the nat2PNat definition

-- The type of parity values - either Even or Odd
data Parity = Even | Odd

-- Even is the opposite of Odd and Odd is the opposite of Even
opposite: Parity -> Parity
opposite Even = Odd
opposite Odd  = Even

-- Calculate the parity of a natural number
parityOf : Nat -> Parity
parityOf Z     = Even
parityOf (S x) = opposite $ parityOf x

-- PNat is a type constructor where PNat Even contains the even numbers, and PNat Odd contains the odd numbers
-- The elements of PNat p can't actually be members of Nat (because Idris only allows items to belong
-- to the type that introduces those items), so I use constructors PZ and PS analogous to the original Z and S.
data PNat : Parity -> Type where
     PZ : PNat Even
     PS : PNat p -> PNat $ opposite p
     
-- PNat values and Nat values are different, but we expect to be able to map from one to the other

-- Calculate the parity of a PNat.
parityOfPNat: {p: Parity} -> (pn: PNat p) -> Parity
parityOfPNat PZ = Even
parityOfPNat (PS pn) = opposite $ parityOfPNat pn

-- The following alternative doesn't work (because the p doesn't exist at run-time, I think):
--parityOfPNat2: {p: Parity} -> (pn: PNat p) -> Parity
--parityOfPNat2 pn = p

-- Map a PNat to a Nat by straightforward induction
pNat2Nat : PNat p -> Nat
pNat2Nat PZ     = Z
pNat2Nat (PS x) = S (pNat2Nat x)

-- Type of Dependent pair of a Parity and a PNat
DPNat : Type
DPNat = (p ** PNat p)

-- Map a Nat to a dependent pair of a Parity and a PNat
nextPNatDpair : DPNat -> DPNat
nextPNatDpair (p ** pn) = (opposite p ** PS pn)

nat2DPNat : Nat -> DPNat
nat2DPNat Z = (Even ** PZ)
nat2DPNat (S k) = nextPNatDpair (nat2DPNat k)

examples_dpnat : List DPNat
examples_dpnat = [(Even ** PZ), nat2DPNat 5]

-- Steps to prove parityOf_gets_parity ...
fst_of_dpair: PNat p -> fst (p**pn) = p
fst_of_dpair x = Refl

nextPNatDpairEquality : (dpNat : DPNat) -> nextPNatDpair dpNat = (opposite (fst dpNat) ** PS (snd dpNat))
nextPNatDpairEquality (x ** pf) = Refl

fstNextPNatDpair : (dpNat : DPNat) -> fst (nextPNatDpair dpNat) = opposite (fst dpNat)
fstNextPNatDpair dpNat = cong {f=fst} (nextPNatDpairEquality dpNat)

parityOf_gets_parity : (n : Nat) -> parityOf n = fst (nat2DPNat n)
parityOf_gets_parity Z = Refl
parityOf_gets_parity (S k) = rewrite parityOf_gets_parity k in rewrite fstNextPNatDpair (nat2DPNat k) in Refl

-- Proofs about 'opposite' ...
opposite_its_own_inverse : (p : Parity) -> p = opposite (opposite p)
opposite_its_own_inverse Even = Refl
opposite_its_own_inverse Odd  = Refl

opposite_opposite_parity_mapper : (p: Parity) -> PNat (opposite (opposite p)) -> PNat p
opposite_opposite_parity_mapper p pnat = rewrite opposite_its_own_inverse p in pnat
     
opposite_is_mono : (p1,p2 : Parity) -> opposite p1 = opposite p2 -> p1 = p2
opposite_is_mono p1 p2 prf = rewrite opposite_its_own_inverse p1 in rewrite opposite_its_own_inverse p2 in cong { f = opposite } prf

-- From Nat to DPNat and back again
snd_nextPNatDpair_dpn: (dpn : DPNat) -> snd (nextPNatDpair dpn) = PS (snd dpn)
snd_nextPNatDpair_dpn (p ** pn) = Refl

sndNat2DpNat : (n : Nat) -> snd (nat2DPNat (S n)) = PS (snd (nat2DPNat n))
sndNat2DpNat n = rewrite snd_nextPNatDpair_dpn (nat2DPNat n) in Refl

pNat2NatSndNat2DpNat : (n : Nat) -> pNat2Nat (snd (nat2DPNat (S n))) = S (pNat2Nat (snd (nat2DPNat n)))
pNat2NatSndNat2DpNat n = rewrite sndNat2DpNat n in Refl

nat2DpNat2Nat : (n : Nat) -> pNat2Nat (snd (nat2DPNat n)) = n
nat2DpNat2Nat Z = Refl
nat2DpNat2Nat (S k) = rewrite pNat2NatSndNat2DpNat k in rewrite nat2DpNat2Nat k in Refl
