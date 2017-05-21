module Integers

%default total

data SignedNat : Type where
  Minus : Nat -> SignedNat
  Plus : Nat -> SignedNat
  
namespace signed_nat
  equals : SignedNat -> SignedNat -> Bool
  equals (Minus k) (Minus j) = k == j
  equals (Minus k) (Plus j) = k == 0 && j == 0
  equals (Plus k) (Minus j) = k == 0 && j == 0
  equals (Plus k) (Plus j) = k == j

Eq SignedNat where
  (==) = signed_nat.equals
  
plus_one: SignedNat -> SignedNat
plus_one (Minus Z) = Plus (S Z)
plus_one (Minus (S k)) = Minus k
plus_one (Plus k) = Plus (S k)

data PeanoInteger : Type where
  Z : PeanoInteger
  P : PeanoInteger -> PeanoInteger
  S : PeanoInteger -> PeanoInteger

nat2PeanoInt : Nat -> PeanoInteger
nat2PeanoInt Z = Z
nat2PeanoInt (S k) = S (nat2PeanoInt k)

minusNat2PeanoInt : Nat -> PeanoInteger
minusNat2PeanoInt Z = Z
minusNat2PeanoInt (S k) = P (minusNat2PeanoInt k)

signedNat2PeanoInt : SignedNat -> PeanoInteger
signedNat2PeanoInt (Minus k) = minusNat2PeanoInt k
signedNat2PeanoInt (Plus k) = nat2PeanoInt k

P_of_normalized : PeanoInteger -> PeanoInteger
P_of_normalized Z = P Z
P_of_normalized (P x) = P (P x)
P_of_normalized (S x) = x

S_of_normalized : PeanoInteger -> PeanoInteger
S_of_normalized Z = S Z
S_of_normalized (S x) = S (S x)
S_of_normalized (P x) = x

normalize : PeanoInteger -> PeanoInteger
normalize Z = Z
normalize (P x) = P_of_normalized (normalize x)
normalize (S x) = S_of_normalized (normalize x)

data Sign = Negative | Zero | Positive

SignOf : PeanoInteger -> Sign
SignOf x with (normalize x)
  | Z = Zero
  | (S y) = Positive
  | (P y) = Negative
  
DepthOfPeanoInteger : PeanoInteger -> Nat
DepthOfPeanoInteger Z = 0
DepthOfPeanoInteger (P x) = S $ DepthOfPeanoInteger x
DepthOfPeanoInteger (S x) = S $ DepthOfPeanoInteger x

Examples : (SignOf (P (S Z)) = Zero, SignOf(S (S Z)) = Positive, SignOf(P (S (P (P Z)))) = Negative)
Examples = (Refl, Refl, Refl)

Abs : PeanoInteger -> Nat
Abs x = DepthOfPeanoInteger $ normalize x
