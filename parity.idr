module Parity

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

namespace parity_arithmetic
          
  plus: Parity -> Parity -> Parity
  plus Even x = x
  plus Odd Even = Odd
  plus Odd Odd = Even

  mult:  Parity -> Parity -> Parity
  mult Odd Odd = Odd
  mult _ _ = Even

-- Calculate the parity of a natural number
parityOf : Nat -> Parity
parityOf Z     = Even
parityOf (S x) = opposite $ parityOf x

Num Parity where
  (+) = parity_arithmetic.plus
  (*) = parity_arithmetic.mult
  fromInteger = \i => parityOf $ fromInteger i
  
parity_addition_commutes: (p1 : Parity) -> (p2 : Parity) -> p1 + p2 = p2 + p1
parity_addition_commutes Even Even = Refl
parity_addition_commutes Even Odd = Refl
parity_addition_commutes Odd Even = Refl
parity_addition_commutes Odd Odd = Refl

even_is_additive_identity: (p : Parity) -> p + Even = p
even_is_additive_identity Even = Refl
even_is_additive_identity Odd = Refl

plus_opposite: (p1 : Parity) -> (p2 : Parity) -> opposite(p1) + p2 = opposite(p1+p2)
plus_opposite Even Even = Refl
plus_opposite Even Odd = Refl
plus_opposite Odd Even = Refl
plus_opposite Odd Odd = Refl

parityOf_is_addition_homomorphism: (n1 : Nat) -> (n2 : Nat) -> parityOf(n1) + parityOf(n2) = parityOf(n1+n2)
parityOf_is_addition_homomorphism Z n2 = Refl
parityOf_is_addition_homomorphism (S k) n2 = rewrite plus_opposite (parityOf k) (parityOf n2) in 
                                              rewrite parityOf_is_addition_homomorphism k n2 in Refl

-- PNat is a type constructor where PNat Even contains the even numbers, and PNat Odd contains the odd numbers
-- The elements of PNat p can't actually be members of Nat (because Idris only allows items to belong
-- to the type that introduces those items), so I use constructors PZ and PS analogous to the original Z and S.
data PNat : Parity -> Type where
     PZ : PNat Even
     PS : PNat p -> PNat $ opposite p
     
pnat_plus: PNat p1 -> PNat p2 -> PNat (p1 + p2)
pnat_plus PZ y = y
pnat_plus {p1=opposite p} {p2} (PS x) y = rewrite plus_opposite p p2 in PS (pnat_plus x y)

-- PNat values and Nat values are different, but we expect to be able to map from one to the other

-- Calculate the parity of a PNat, by induction on PS
parityOfPNat: {p: Parity} -> (pn: PNat p) -> Parity
parityOfPNat PZ = Even
parityOfPNat (PS pn) = opposite $ parityOfPNat pn

-- Get the parity from the type itself, which works as longs as the type variable {p} is brought into scope
parityOfPNat2: {p: Parity} -> (pn: PNat p) -> Parity
parityOfPNat2 {p} pn = p

pnat_parity_functions_equal: {p: Parity} -> (pn: PNat p) -> parityOfPNat pn = parityOfPNat2 pn
pnat_parity_functions_equal PZ = Refl
pnat_parity_functions_equal (PS p1) = rewrite pnat_parity_functions_equal p1 in Refl

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
opposite_its_own_inverse : (p : Parity) -> opposite (opposite p) = p
opposite_its_own_inverse Even = Refl
opposite_its_own_inverse Odd  = Refl

opposite_opposite_parity_mapper : (p: Parity) -> PNat (opposite (opposite p)) -> PNat p
opposite_opposite_parity_mapper p pnat = rewrite sym $ opposite_its_own_inverse p in pnat
     
opposite_is_mono : (p1,p2 : Parity) -> opposite p1 = opposite p2 -> p1 = p2
opposite_is_mono p1 p2 prf = rewrite sym $ opposite_its_own_inverse p1 in 
                             rewrite sym $ opposite_its_own_inverse p2 in 
                             cong { f = opposite } prf

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

-- From DPNat to Nat and back again
p_pNat2Nat2dpNat : (p : Parity) -> (pn : PNat p) -> nat2DPNat (pNat2Nat pn) = (p ** pn)
p_pNat2Nat2dpNat Even PZ = Refl
p_pNat2Nat2dpNat (opposite p1) (PS pn1) = rewrite p_pNat2Nat2dpNat p1 pn1 in Refl

dpNat2Nat2dpNat : (dpn : DPNat) -> nat2DPNat (pNat2Nat (snd dpn)) = dpn
dpNat2Nat2dpNat (p ** pn) = p_pNat2Nat2dpNat p pn

-- Some abstractions

is_an_involution: {t : Type} ->  (f : t -> t) -> Type
is_an_involution {t} f = (x: t) -> f (f x) = x

opposite_is_an_involution: is_an_involution Parity.opposite
opposite_is_an_involution = opposite_its_own_inverse

is_left_inverse: {t1: Type} -> {t2: Type} -> (f : t1 -> t2) -> (g : t2 -> t1) -> Type
is_left_inverse {t1} {t2} f g = (x: t2) -> f (g x) = x

pNat2Nat_snd : (dpn : DPNat) -> Nat
pNat2Nat_snd = \dpn => pNat2Nat (snd dpn)

nat2DPNat_is_left_inverse_of_pNat2Nat_snd: is_left_inverse Parity.nat2DPNat Parity.pNat2Nat_snd
nat2DPNat_is_left_inverse_of_pNat2Nat_snd = dpNat2Nat2dpNat

pNat2Nat_snd_is_left_inverse_of_nat2DPNat: is_left_inverse Parity.pNat2Nat_snd Parity.nat2DPNat
pNat2Nat_snd_is_left_inverse_of_nat2DPNat = nat2DpNat2Nat

are_inverses_of_each_other: {t1: Type} -> {t2: Type} -> (f : t1 -> t2) -> (g : t2 -> t1) -> Type
are_inverses_of_each_other f g = (is_left_inverse f g, is_left_inverse g f)

pNat2Nat_snd_and_nat2DPNat_are_inverses: are_inverses_of_each_other Parity.nat2DPNat Parity.pNat2Nat_snd
pNat2Nat_snd_and_nat2DPNat_are_inverses = (nat2DPNat_is_left_inverse_of_pNat2Nat_snd, pNat2Nat_snd_is_left_inverse_of_nat2DPNat)
