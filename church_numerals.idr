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

church_mult : EndomorphismApplier -> EndomorphismApplier -> EndomorphismApplier
church_mult ea1 ea2 t f = ea1 t $ ea2 t f

church_mult_example : (church_mult (church_numeral 2) (church_numeral 3)) Nat S Z = 6
church_mult_example = Refl
