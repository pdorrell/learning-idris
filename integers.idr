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
is_inverse_of {a} f f' = (x : a) -> (f (f' x)) == x = True

are_inverses : Eq a => (a -> a) -> (a -> a) -> Type
are_inverses f f' = (is_inverse_of f f', is_inverse_of f' f)

nat_eq_reflexive : (n : Nat) -> n == n = True
nat_eq_reflexive Z = Refl
nat_eq_reflexive (S k) = nat_eq_reflexive k

signed_nat_eq_reflexive : (x : SignedNat) -> x == x = True
signed_nat_eq_reflexive (Minus k) = nat_eq_reflexive k
signed_nat_eq_reflexive (Plus k) = nat_eq_reflexive k

plus_one_is_inverse_of_minus_one: is_inverse_of Integers.plus_one Integers.minus_one
plus_one_is_inverse_of_minus_one x = lemma x where
  lemma: (y : SignedNat) -> plus_one (minus_one y) == y = True
  lemma (Minus k) = nat_eq_reflexive k
  lemma (Plus Z) = Refl
  lemma (Plus (S k)) = nat_eq_reflexive k

minus_one_is_inverse_of_plus_one: is_inverse_of Integers.minus_one Integers.plus_one
minus_one_is_inverse_of_plus_one x = lemma x where
  lemma: (y : SignedNat) -> minus_one (plus_one y) == y = True
  lemma (Minus Z) = Refl
  lemma (Minus (S k)) = nat_eq_reflexive k
  lemma (Plus k) = nat_eq_reflexive k

are_inverses_plus_and_minus_one : are_inverses Integers.plus_one Integers.minus_one
are_inverses_plus_and_minus_one = (plus_one_is_inverse_of_minus_one, minus_one_is_inverse_of_plus_one)

data FunctionAndInverse : (a : Type) -> Type where
  FunAndInverse : Eq a => (f : a -> a) -> (f' : a -> a) -> (are_inverses f f') -> FunctionAndInverse a
  
interface BidirectionalRepeater t where
   repeat : t -> (a -> a, a -> a) -> a -> a
   
bi_repeat : BidirectionalRepeater t => t -> FunctionAndInverse a -> a -> a
bi_repeat r (FunAndInverse f f' y) x = repeat r (f, f') x

equal_bi_repeaters : (BidirectionalRepeater t1, BidirectionalRepeater  t2) => (r1 : t1) -> (r2 : t2) -> Type
equal_bi_repeaters r1 r2 = (a : Type) -> Eq a -> (fai : FunctionAndInverse a) -> (x : a) -> bi_repeat r1 fai x == bi_repeat r2 fai x = True

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

Eq PeanoInteger where
  (==) x y = peanoInt2SignedNat x == peanoInt2SignedNat y
