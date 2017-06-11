%default total

-- repeatedly apply function f to an initial value x n times
repeat : (n : Nat) -> (f: t -> t) -> (x : t) -> t
repeat Z f x = x
repeat (S k) f x = f (repeat k f x)

-- use 'repeat' to reconstruct a Nat n by applying S to Z n times
repeat_reconstructs_a_nat: (n: Nat) -> repeat n S Z = n
repeat_reconstructs_a_nat Z = Refl
repeat_reconstructs_a_nat (S k) = cong {f=S} $ repeat_reconstructs_a_nat k

-- An EndomorphismApplier is a thing, which for any type,
-- and given an endormorphism on that type and an initial value of that type,
-- returns a value of the same type.
-- (Note: EndomorphismApplier might in principle contain things other than Church numerals,
--  but Parametricity possibly prevents this in practice, even though we can't prove that inside Idris.)
EndomorphismApplier : Type
EndomorphismApplier = (t: Type) -> (t -> t) -> t -> t

-- Representation of 0 as a church numeral
church_zero: EndomorphismApplier
church_zero t f x = x

-- Representation of S as a function from Church numeral to Church numeral
church_succ : EndomorphismApplier -> EndomorphismApplier
church_succ ea t f x = f (ea t f x)

-- Function to create the Church numeral from a Nat
church_numeral : Nat -> EndomorphismApplier
church_numeral Z = church_zero
church_numeral (S k) = church_succ (church_numeral k)

-- Function to recreate Nat from Church numeral
church_numeral_to_nat : EndomorphismApplier -> Nat
church_numeral_to_nat ea = ea Nat S Z

-- From Nat to Church numeral and back to Nat
nat2church_numeral2nat : (n : Nat) -> church_numeral_to_nat (church_numeral n) = n
nat2church_numeral2nat Z = Refl
nat2church_numeral2nat (S k) = cong {f=S} $ nat2church_numeral2nat k

-- Functional definition of Church numeral addition
church_plus : EndomorphismApplier -> EndomorphismApplier -> EndomorphismApplier
church_plus ea1 ea2 t f x = ea1 t f $ ea2 t f x

-- An example: 3+4=7
church_plus_example : church_numeral_to_nat (church_plus (church_numeral 3) (church_numeral 4)) = 7
church_plus_example = Refl

-- A lemma about mixed addition of Church numeral and a Nat
church_plus_lemma : (k : Nat) -> (m : Nat) -> church_numeral k Nat S m = plus k m
church_plus_lemma Z m = Refl
church_plus_lemma (S k) m = cong {f=S} $ church_plus_lemma k m

-- Church numeral addition gives the same result as Nat addition
church_plus_2_nat_plus: (n : Nat) -> (m : Nat) -> church_numeral_to_nat (church_plus (church_numeral n) (church_numeral m)) = n + m
church_plus_2_nat_plus Z m = nat2church_numeral2nat m
church_plus_2_nat_plus (S k) m = cong {f=S} $ rewrite nat2church_numeral2nat m in church_plus_lemma k m

-- Functional definition of Church numeral multiplication
church_mult : EndomorphismApplier -> EndomorphismApplier -> EndomorphismApplier
church_mult ea1 ea2 t f = ea1 t $ ea2 t f

-- An example: 2*3=6
church_mult_example : church_numeral_to_nat (church_mult (church_numeral 2) (church_numeral 3)) = 6
church_mult_example = Refl

-- Churchified k*m = Nat k*m
n_times_m_lemma: (n : Nat) -> (m : Nat) ->  church_numeral n Nat (church_numeral m Nat S) 0 = mult n m
n_times_m_lemma Z m = Refl
n_times_m_lemma (S k) m = rewrite n_times_m_lemma k m in church_plus_lemma m (mult k m)

-- Church numeral multiplication gives the same result as Nat multiplication
church_mult_2_nat_mult: (n : Nat) -> (m : Nat) -> church_numeral_to_nat (church_mult (church_numeral n) (church_numeral m)) = n * m
church_mult_2_nat_mult n m = n_times_m_lemma n m
