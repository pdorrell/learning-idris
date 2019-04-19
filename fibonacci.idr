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
-- The state includes proofs that Fibonacci_n is fib(n) and Fibonacci_sn is fib(n+1)
record FibState (n: Nat) where
 constructor MkFibState
 Fibonacci_n : Nat
 Fibonacci_sn : Nat
 Fibonacci_n_prf : Fibonacci_n = fibonacci n
 Fibonacci_sn_prf : Fibonacci_sn = fibonacci (S n)

-- The initial state holding fib(0) & fib(1)
fib_state_0 : FibState 0
fib_state_0 = MkFibState 1 1 Refl Refl

-- How to get to the next state from the previous state, including the required proofs
next_fib_state : FibState n -> FibState (S n)
next_fib_state {n} (MkFibState fibonacci_n fibonacci_sn Fibonacci_n_prf Fibonacci_sn_prf) = 
  let e1 = the (fibonacci (S (S n)) = fibonacci n + fibonacci (S n)) Refl
      e2 = the (fibonacci (S (S n)) = fibonacci_n + fibonacci (S n)) $ rewrite Fibonacci_n_prf in e1
      e3 = the (fibonacci (S (S n)) = fibonacci_n + fibonacci_sn) $ rewrite Fibonacci_sn_prf in e2
  in MkFibState fibonacci_sn (fibonacci_n + fibonacci_sn) Fibonacci_sn_prf (sym e3)

-- The function to calculate the nth state
fib_state_n : (n : Nat) -> FibState n
fib_state_n Z = fib_state_0
fib_state_n (S k) = next_fib_state $ fib_state_n k

-- The optimized version of the Fibonacci function, that calculates the (n-1)th
-- intermediate state, and then extracts the second value of the final state
-- to be fib(n)
fibonacci2 : Nat -> Nat 
fibonacci2 Z = 1
fibonacci2 (S k) = Fibonacci_sn $ fib_state_n k

-- The fairly simple proof that fibonacci2 and fibonacci give the same result.
-- (Most of the work has already been done inside next_fib_state.)
fib_eq_fib2 : (n: Nat) -> fibonacci2 n = fibonacci n
fib_eq_fib2 Z = Refl
fib_eq_fib2 (S k) = Fibonacci_sn_prf $ fib_state_n k


-- A slightly simpler but less optimized version
-- (Less optimized because it does one more update step than it needs to,
--  and reads the answer out of Fibonacci_n instead of Fibonacci_sn,
--  in effect wasting the work it did to compute the last value of Fibonacci_sn.)
fibonacci3 : Nat -> Nat 
fibonacci3 n =  Fibonacci_n $ fib_state_n n

fib_eq_fib3 : (n: Nat) -> fibonacci3 n = fibonacci n
fib_eq_fib3 n = Fibonacci_n_prf $ fib_state_n n

