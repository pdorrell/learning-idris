module Fibonacci

%default total

-- The inefficient but mathematically simply definition of the Fibonacci function
fibonacci: Nat -> Nat
fibonacci Z = 1
fibonacci (S Z) = 1
fibonacci (S (S n)) = (fibonacci n) + (fibonacci (S n))

-- A test example
test: fibonacci 6 = 13
test = Refl

-- An intermediate state for a more efficient calculation,
-- where we retain the last two values calculated.
-- The state includes a proof that X is fib(n) and Y is fib(n+1)
record FibState (n: Nat) where
 constructor MkFibState
 X : Nat
 Y : Nat
 x_is_fib_n : X = fibonacci n
 y_is_fib_sn : Y = fibonacci (S n)

-- The initial state holding fib(0) & fib(10
fib_state_0 : FibState 0
fib_state_0 = MkFibState 1 1 Refl Refl

-- How to get to the next state from the previous state, including the required proofs
next_fib_state : FibState n -> FibState (S n)
next_fib_state {n} (MkFibState x y x_is_fib_n y_is_fib_sn) = 
  let e1 = the (fibonacci (S (S n)) = fibonacci n + fibonacci (S n)) Refl
      e2 = the (fibonacci (S (S n)) = x + fibonacci (S n)) $ rewrite x_is_fib_n in e1
      e3 = the (fibonacci (S (S n)) = x + y) $ rewrite y_is_fib_sn in e2
  in MkFibState y (x + y) y_is_fib_sn (sym e3)

-- The function to calculate the nth state
fib_state_n : (n : Nat) -> FibState n
fib_state_n Z = fib_state_0
fib_state_n (S k) = next_fib_state $ fib_state_n k

-- The optimized version of the Fibonacci function, that calculates the (n-1)th
-- intermediate state, and then extracts the second value of the final state
-- to be fib(n)
fibonacci2 : Nat -> Nat 
fibonacci2 Z = 1
fibonacci2 (S k) = Y $ fib_state_n k

-- The fairly simple proof that fibonacci2 and fibonacci give the same result.
-- (Most of the work has already been done inside next_fib_state.)
fib_eq_fib2 : (n: Nat) -> fibonacci2 n = fibonacci n
fib_eq_fib2 Z = Refl
fib_eq_fib2 (S k) = y_is_fib_sn $ fib_state_n k
