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

minus_one: SignedNat -> SignedNat
minus_one (Minus k) = Minus (S k)
minus_one (Plus Z) = Minus (S Z)
minus_one (Plus (S k)) = Plus k

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

is_inverse_of: Eq a => (a -> a) -> (a -> a) -> Type
is_inverse_of {a} f f' = (x : a) -> (f (f' x)) = x

are_inverses : Eq a => (a -> a) -> (a -> a) -> Type
are_inverses f f' = (is_inverse_of f f', is_inverse_of f' f)

data FunctionAndInverse : (a : Type) -> Type where
  FunAndInverse : Eq a => (f : a -> a) -> (f' : a -> a) -> (are_inverses f f') -> FunctionAndInverse a
  
apply_fun : FunctionAndInverse a -> a -> a
apply_fun (FunAndInverse f f' prf) y = f y

unapply_fun : FunctionAndInverse a -> a -> a
unapply_fun (FunAndInverse f f' prf) y = f' y

interface BidirectionalRepeater t where
   repeat : t -> (a -> a, a -> a) -> a -> a

repeat_peano_int : PeanoInteger -> (a -> a, a -> a) -> a -> a
repeat_peano_int Z (f, f') y = y
repeat_peano_int (P x) (f, f') y = f' $ repeat_peano_int x (f, f') y
repeat_peano_int (S x) (f, f') y = f $ repeat_peano_int x (f, f') y

BidirectionalRepeater PeanoInteger where
  repeat = repeat_peano_int

repeat_int: Nat -> (f: a -> a) -> a -> a
repeat_int Z f x = x
repeat_int (S k) f x = f $ repeat_int k f x

repeat_signed_nat : SignedNat -> (a -> a, a -> a) -> a -> a
repeat_signed_nat (Minus k) (f, f') y = repeat_int k f' y
repeat_signed_nat (Plus k) (f, f') y = repeat_int k f y

BidirectionalRepeater SignedNat where
  repeat = repeat_signed_nat
  


peanoInt2SignedNat: PeanoInteger -> SignedNat
peanoInt2SignedNat x = repeat_peano_int x (plus_one, minus_one) (Plus Z)

p_of_normalized : PeanoInteger -> PeanoInteger
p_of_normalized Z = P Z
p_of_normalized (P x) = P (P x)
p_of_normalized (S x) = x

s_of_normalized : PeanoInteger -> PeanoInteger
s_of_normalized Z = S Z
s_of_normalized (S x) = S (S x)
s_of_normalized (P x) = x

normalize : PeanoInteger -> PeanoInteger
normalize Z = Z
normalize (P x) = p_of_normalized (normalize x)
normalize (S x) = s_of_normalized (normalize x)

data Sign = Negative | Zero | Positive

sign_of : PeanoInteger -> Sign
sign_of x with (normalize x)
  | Z = Zero
  | (S y) = Positive
  | (P y) = Negative
  
depth_of_peano_integer : PeanoInteger -> Nat
depth_of_peano_integer Z = 0
depth_of_peano_integer (P x) = S $ depth_of_peano_integer x
depth_of_peano_integer (S x) = S $ depth_of_peano_integer x

sign_of_examples : (sign_of (P (S Z)) = Zero, sign_of(S (S Z)) = Positive, sign_of(P (S (P (P Z)))) = Negative)
sign_of_examples = (Refl, Refl, Refl)

abs : PeanoInteger -> Nat
abs x = depth_of_peano_integer $ normalize x

signed_int : Sign -> Nat -> PeanoInteger
signed_int Negative Z = Z
signed_int Negative (S n) = P (signed_int Negative n)
signed_int Zero n = Z
signed_int Positive Z = Z
signed_int Positive (S n) = S (signed_int Positive n)


