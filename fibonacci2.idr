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

FirstIfEven: (p : Parity) -> (n1 : t) -> (n2 : t) -> t
FirstIfEven Even n1 n2 = n1
FirstIfEven Odd n1 n2 = n2

SwappedIfOdd: (p : Parity) -> (p : Pair t t) -> Pair t t
SwappedIfOdd Even (x, y) = (x, y)
SwappedIfOdd Odd (x, y) = (y, x)
                         
record FibWithParityState (n: Nat) where
 constructor MkFibWithParityState
 Parity_n : Parity
 Fibonacci_even_n_or_sn : Nat
 Fibonacci_odd_n_or_sn : Nat
 Parity_n_prf : ParityOf n = Parity_n
 Fibonacci_n_and_sn_prf : (Fibonacci_even_n_or_sn, Fibonacci_odd_n_or_sn) = SwappedIfOdd Parity_n (fibonacci n, fibonacci (S n))
 
fib_with_parity_state_0 : FibWithParityState 0
fib_with_parity_state_0 = MkFibWithParityState Even 1 1 Refl Refl

fib_with_parity_state_1 : FibWithParityState 1
fib_with_parity_state_1 = MkFibWithParityState Odd 2 1 Refl Refl

fib_with_parity_state_2 : FibWithParityState 2
fib_with_parity_state_2 = MkFibWithParityState Even 2 3 Refl Refl

fib_with_parity_state_3 : FibWithParityState 3
fib_with_parity_state_3 = MkFibWithParityState Odd 5 3 Refl Refl

next_fib_with_parity_state : FibWithParityState n -> FibWithParityState (S n)
next_fib_with_parity_state {n} (MkFibWithParityState Even fib_even fib_odd n_is_even fib_s_sn_prf) = 
  let e1 = the (ParityOf (S n) = Odd) $ rewrite n_is_even in Refl
      e2 = the ((fib_even, fib_odd) = (fibonacci n, fibonacci (S n))) $ fib_s_sn_prf
      e3 = the (fib_even = fibonacci n) $ cong {f=fst} e2
      e4 = the (fib_odd = fibonacci (S n)) $ cong {f=snd} e2
      e7 = the (fib_even + fib_odd = fibonacci (S (S n))) $ rewrite e3 in rewrite e4 in Refl
      e5 = the ((fib_even + fib_odd, fib_odd) = (fibonacci (S (S n)), fibonacci (S n))) $ rewrite e7 in rewrite e4 in Refl
  in MkFibWithParityState Odd (fib_even + fib_odd) fib_odd e1 e5
next_fib_with_parity_state {n} (MkFibWithParityState Odd fib_even fib_odd n_is_odd fib_s_sn_prf) = ?hole_2

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
