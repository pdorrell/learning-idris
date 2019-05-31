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
      e5 = the (fib_even + fib_odd = fibonacci (S (S n))) $ rewrite e3 in rewrite e4 in Refl
      e6 = the ((fib_even + fib_odd, fib_odd) = (fibonacci (S (S n)), fibonacci (S n))) $ rewrite e5 in rewrite e4 in Refl
  in MkFibWithParityState Odd (fib_even + fib_odd) fib_odd e1 e6
next_fib_with_parity_state {n} (MkFibWithParityState Odd fib_even fib_odd n_is_odd fib_s_sn_prf) =
  let e1 = the (ParityOf (S n) = Even) $ rewrite n_is_odd in Refl
      e2 = the ((fib_even, fib_odd) = (fibonacci (S n), fibonacci n)) $ fib_s_sn_prf
      e3 = the (fib_even = fibonacci (S n)) $ cong {f=fst} e2
      e4 = the (fib_odd = fibonacci n) $ cong {f=snd} e2
      e5 = the (fib_odd + fib_even = fibonacci (S (S n))) $ rewrite e3 in rewrite e4 in Refl
      e6 = the ((fib_even, fib_odd + fib_even) = (fibonacci (S n), fibonacci (S (S n)))) $ rewrite e5 in rewrite e3 in Refl
  in MkFibWithParityState Even fib_even (fib_odd + fib_even) e1 e6
  
fib_with_parity_state_n : (n : Nat) -> FibWithParityState n
fib_with_parity_state_n Z = fib_with_parity_state_0
fib_with_parity_state_n (S k) = next_fib_with_parity_state $ fib_with_parity_state_n k

fib_n_of_fib_with_parity_state : FibWithParityState n -> Nat
fib_n_of_fib_with_parity_state (MkFibWithParityState Even fib_even_n_or_sn _ _ _) = fib_even_n_or_sn
fib_n_of_fib_with_parity_state (MkFibWithParityState Odd _ fib_odd_n_or_sn _ _) = fib_odd_n_or_sn

fibonacci2 : (n : Nat) -> Nat
fibonacci2 n = fib_n_of_fib_with_parity_state (fib_with_parity_state_n n)

fib2_eq_fib_for_n : (n : Nat) -> Type
fib2_eq_fib_for_n n = fibonacci2 n = fibonacci n

fib2_eq_fib_for_3 : fib2_eq_fib_for_n 3
fib2_eq_fib_for_3 = Refl

fib2_eq_fib_for_8 : fib2_eq_fib_for_n 8
fib2_eq_fib_for_8 = Refl

