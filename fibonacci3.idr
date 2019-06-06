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

record FibWithSwappableState (n: Nat) where
 constructor MkFibWithSwappableState
 Swapped : Bool
 Fibonacci_n_or_sn : Nat
 Fibonacci_sn_or_n : Nat
 Not_swapped_prf : Swapped = False -> (Fibonacci_n_or_sn = fibonacci n, Fibonacci_sn_or_n = fibonacci (S n))
 Swapped_prf : Swapped = True -> (Fibonacci_n_or_sn = fibonacci (S n), Fibonacci_sn_or_n = fibonacci n)
 
-- examples
fib_with_swappable_state_0 : FibWithSwappableState 0
fib_with_swappable_state_0 = MkFibWithSwappableState False 1 1 (const (Refl, Refl)) absurd

fib_with_swappable_state_3 : FibWithSwappableState 3
fib_with_swappable_state_3 = MkFibWithSwappableState True 5 3 absurd (const (Refl, Refl))

fib_with_swappable_state_3b : FibWithSwappableState 3
fib_with_swappable_state_3b = MkFibWithSwappableState False 3 5 (const (Refl, Refl)) absurd

-- end of examples

next_fib_with_swappable_state : FibWithSwappableState n -> FibWithSwappableState (S n)

next_fib_with_swappable_state {n} (MkFibWithSwappableState False fib_n_or_sn fib_sn_or_n not_swapped_prf _) = 
  let (e1, e2) = the (fib_n_or_sn = fibonacci n, fib_sn_or_n = fibonacci (S n)) $ not_swapped_prf Refl
      e3 = the (plus fib_n_or_sn fib_sn_or_n = plus (fibonacci n) (fibonacci (S n))) $ rewrite e1 in rewrite e2 in Refl
  in MkFibWithSwappableState True (fib_n_or_sn + fib_sn_or_n) fib_sn_or_n absurd (const (e3, e2))
  
next_fib_with_swappable_state {n} (MkFibWithSwappableState True fib_n_or_sn fib_sn_or_n _ swapped_prf) = 
  let (e1, e2) = swapped_prf Refl
      e3 = the (plus fib_sn_or_n fib_n_or_sn = plus (fibonacci n) (fibonacci (S n))) $ rewrite e2 in rewrite e1 in Refl
  in MkFibWithSwappableState False fib_n_or_sn (fib_sn_or_n + fib_n_or_sn) (const (e1, e3)) absurd

fib_with_swappable_state_n : (n : Nat) -> FibWithSwappableState n
fib_with_swappable_state_n Z = fib_with_swappable_state_0
fib_with_swappable_state_n (S k) = next_fib_with_swappable_state (fib_with_swappable_state_n k)

fib_n_of_swappable_state : FibWithSwappableState n -> Nat
fib_n_of_swappable_state (MkFibWithSwappableState False fib_n_or_sn _ _ _) = fib_n_or_sn
fib_n_of_swappable_state (MkFibWithSwappableState True _ fib_sn_or_n _ _) = fib_sn_or_n

fibonacci2 : (n : Nat) -> Nat
fibonacci2 n = fib_n_of_swappable_state (fib_with_swappable_state_n n)

fib2_eq_fib_for_n : (n : Nat) -> Type
fib2_eq_fib_for_n n = fibonacci2 n = fibonacci n

-- examples
fib2_eq_fib_for_3 : fib2_eq_fib_for_n 3
fib2_eq_fib_for_3 = Refl

fib2_eq_fib_for_8 : fib2_eq_fib_for_n 8
fib2_eq_fib_for_8 = Refl
-- end of examples

lemma : (fib_swappable_state : FibWithSwappableState n) -> fib_n_of_swappable_state fib_swappable_state = fibonacci n
lemma {n = n} (MkFibWithSwappableState False fib_n_or_sn fib_sn_or_n not_swapped_prf _) = fst (not_swapped_prf Refl)
lemma {n = n} (MkFibWithSwappableState True fib_n_or_sn fib_sn_or_n _ swapped_prf) = snd (swapped_prf Refl)

fib2_eq_fib : (n : Nat) -> fib2_eq_fib_for_n n
fib2_eq_fib n = lemma {n=n} (fib_with_swappable_state_n n)
