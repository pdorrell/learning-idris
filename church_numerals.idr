%default total

repeat : Nat -> (t -> t) -> t -> t
repeat Z f x = x
repeat (S k) f x = f (repeat k f x)

repeat_reconstructs_a_nat: (n: Nat) -> repeat Z S n = n
repeat_reconstructs_a_nat Z = Refl
repeat_reconstructs_a_nat (S k) = Refl

-- An EndomorphismApplier is a thing, which for any type,
-- and given an endormorphism on that type and an initial value of that type,
-- returns a value of the same type.
EndomorphismApplier : Type
EndomorphismApplier = (t: Type) -> (t -> t) -> t -> t

church_zero: EndomorphismApplier
church_zero t f x = x

church_succ : EndomorphismApplier -> EndomorphismApplier
church_succ ea t f x = f (ea t f x)

church_numeral : Nat -> EndomorphismApplier
church_numeral Z = church_zero
church_numeral (S k) = church_succ (church_numeral k)

church_numeral_1_to_1: (n : Nat) -> (church_numeral n) Nat S Z = n
church_numeral_1_to_1 Z = Refl
church_numeral_1_to_1 (S k) = cong {f=S} $ church_numeral_1_to_1 k

church_plus : EndomorphismApplier -> EndomorphismApplier -> EndomorphismApplier
church_plus ea1 ea2 t f x = ea1 t f $ ea2 t f x

church_plus_example : (church_plus (church_numeral 3) (church_numeral 4)) Nat S Z = 7
church_plus_example = Refl

church_plus_lemma : (k : Nat) -> (m : Nat) -> church_numeral k Nat S m = plus k m
church_plus_lemma Z m = Refl
church_plus_lemma (S k) m = cong {f=S} $ church_plus_lemma k m

church_plus_2_nat_plus: (n : Nat) -> (m : Nat) -> church_plus (church_numeral n) (church_numeral m) Nat S Z = n + m
church_plus_2_nat_plus Z m = church_numeral_1_to_1 m
church_plus_2_nat_plus (S k) m = cong {f=S} $ rewrite church_numeral_1_to_1 m in church_plus_lemma k m

church_mult : EndomorphismApplier -> EndomorphismApplier -> EndomorphismApplier
church_mult ea1 ea2 t f = ea1 t $ ea2 t f

church_mult_example : (church_mult (church_numeral 2) (church_numeral 3)) Nat S Z = 6
church_mult_example = Refl

mult_0 : (k : Nat) -> mult k 0 = 0
mult_0 Z = Refl
mult_0 (S k) = mult_0 k

lemma1 : (k : Nat) -> church_numeral k Nat (church_zero Nat S) 0 = 0
lemma1 Z = Refl
lemma1 (S k) = lemma1 k

lemma2 : (n : Nat) -> (k : Nat) -> mult (S k) n = plus n (mult k n)
lemma2 n k = Refl

lemma3:(k : Nat) -> (m : Nat) ->  church_numeral k Nat (church_numeral m Nat S) 0 = mult k m
lemma3 Z m = Refl
lemma3 (S k) m = rewrite lemma3 k m in church_plus_lemma m (mult k m)

church_mult_s_lemma : (k : Nat) -> (m : Nat) -> church_numeral m Nat S (church_numeral k Nat (church_numeral m Nat S) 0) = plus m (mult k m)
church_mult_s_lemma k m = rewrite lemma3 k m in church_plus_lemma m (mult k m)

church_mult_2_nat_mult: (n : Nat) -> (m : Nat) -> church_mult (church_numeral n) (church_numeral m) Nat S Z = n * m
church_mult_2_nat_mult Z m = Refl
church_mult_2_nat_mult (S k) m = church_mult_s_lemma k m


