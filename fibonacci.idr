module Fibonacci

%default total

fibonacci: Nat -> Nat
fibonacci Z = 1
fibonacci (S Z) = 1
fibonacci (S (S n)) = (fibonacci n) + (fibonacci (S n))

test: fibonacci 6 = 13
test = Refl

record FibState (n: Nat) where
 constructor MkFibState
 x : Nat
 y : Nat
 x_is_fib_n : fibonacci n = x
 y_is_fib_n1 : fibonacci (S n) = y

fib_state_0 : FibState 0
fib_state_0 = MkFibState 1 1 Refl Refl

next_fib_state : FibState n -> FibState (S n)
next_fib_state {n} (MkFibState x y x_is_fib_n y_is_fib_n1) = 
  let e1 = the (fibonacci (S (S n)) = fibonacci n + fibonacci (S n)) Refl
      e2 = the (fibonacci (S (S n)) = x + fibonacci (S n)) $ rewrite sym x_is_fib_n in e1
      e3 = the (fibonacci (S (S n)) = x + y) $ rewrite sym y_is_fib_n1 in e2
  in MkFibState y (x + y) y_is_fib_n1 e3


