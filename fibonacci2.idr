module Fibonacci

%default total

-- The inefficient but mathematically simple definition of the Fibonacci function
fibonacci: Nat -> Nat
fibonacci Z = 1
fibonacci (S Z) = 1
fibonacci (S (S n)) = (fibonacci n) + (fibonacci (S n))

-- Some test examples
test: [fibonacci 5, fibonacci 6, fibonacci 7, fibonacci 10] = [8, 13, 21, 89]
test = Refl

data Parity = Even | Odd

Opposite: Parity -> Parity
Opposite Even = Odd
Opposite Odd = Even

ParityOf: (n : Nat) -> Parity
ParityOf Z = Even
ParityOf (S k) = Opposite $ ParityOf k

SOrSnWithParity : (n : Nat) -> (p : Parity) -> Nat
SOrSnWithParity n Even = case (ParityOf n) of
                         Even => n
                         Odd => S n
SOrSnWithParity n Odd = case (ParityOf n) of
                         Even => S n
                         Odd => n
     
record FibWitParityState (n: Nat) where
 constructor MkFibWitParityState
 Parity_n : Parity
 Fibonacci_even_n_or_sn : Nat
 Fibonacci_odd_n_or_sn : Nat
 Parity_n_prf : Parity_n = ParityOf n
 Fibonacci_even_n_or_sn_prf : Fibonacci_even_n_or_sn = fibonacci (SOrSnWithParity n Even)
 Fibonacci_odd_n_or_sn_prf : Fibonacci_odd_n_or_sn = fibonacci (SOrSnWithParity n Odd)
 
fib_with_parity_state_0 : FibWitParityState 0
fib_with_parity_state_0 = MkFibWitParityState Even 1 1 Refl Refl Refl

next_fib_with_parity_state : FibWitParityState n -> FibWitParityState (S n)
next_fib_with_parity_state {n} (MkFibWitParityState Even fib_even fib_odd n_is_even fib_even_prf fib_odd_prf) = 
  let e1 = the (ParityOf (S n) = Opposite (ParityOf n)) Refl
      e2 = the (Opposite Even = Opposite $ ParityOf n) $ cong n_is_even
      e3 = the (Odd = Opposite Even) Refl
      e4 = the (Odd = ParityOf (S n)) $ trans e3 $ trans e2 $ sym e1
  in MkFibWitParityState Odd fib_even (fib_odd + fib_even) e4 ?h2 ?h3
next_fib_with_parity_state {n} (MkFibWitParityState Odd fib_even fib_odd n_is_odd fib_even_prf fib_odd_prf) = ?hole_2

-- An intermediate state for a more efficient calculation,
-- where we retain the last two values calculated.
-- The state includes proofs that Fibonacci_n is fibonacci(n) and Fibonacci_sn is fibonacci(n+1)
record FibState (n: Nat) where
 constructor MkFibState
 Fibonacci_n : Nat
 Fibonacci_sn : Nat
 Fibonacci_n_prf : Fibonacci_n = fibonacci n
 Fibonacci_sn_prf : Fibonacci_sn = fibonacci (S n)

{-
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

-- An optimized version of the Fibonacci function, that calculates the (n-1)th
-- intermediate state, and then extracts the second value of the final state
-- to be fib(n)
fibonacci2 : Nat -> Nat 
fibonacci2 Z = 1
fibonacci2 (S k) = Fibonacci_sn $ fib_state_n k

-- The fairly simple proof that fibonacci2 and fibonacci give the same result.
-- (Most of the work has already been done inside next_fib_state.)
fib2_eq_fib : (n: Nat) -> fibonacci2 n = fibonacci n
fib2_eq_fib Z = Refl
fib2_eq_fib (S k) = Fibonacci_sn_prf $ fib_state_n k


-- A slightly simpler but less optimized version
-- (Less optimized because it does one more update step than it needs to,
--  and reads the answer out of Fibonacci_n instead of Fibonacci_sn,
--  in effect wasting the work it did to compute the last value of Fibonacci_sn.)
fibonacci3 : Nat -> Nat 
fibonacci3 n =  Fibonacci_n $ fib_state_n n

fib3_eq_fib : (n: Nat) -> fibonacci3 n = fibonacci n
fib3_eq_fib n = Fibonacci_n_prf $ fib_state_n n

-}
