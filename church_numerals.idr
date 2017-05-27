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

