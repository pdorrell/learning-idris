module Fibonacci

%default total

fibonacci: Nat -> Nat
fibonacci Z = 1
fibonacci (S Z) = 1
fibonacci (S (S n)) = (fibonacci n) + (fibonacci (S n))


test: fibonacci 6 = 13
test = Refl
