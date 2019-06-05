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

SwappedIfOdd: (p : Parity) -> (p : Pair t t) -> Pair t t
SwappedIfOdd Even = id
SwappedIfOdd Odd = swap
                         
record FibWithParityState (n: Nat) where
 constructor MkFibWithParityState
 Parity_n : Parity
 Fibonacci_even_n_or_sn : Nat
 Fibonacci_odd_n_or_sn : Nat
 Parity_n_prf : ParityOf n = Parity_n
 Fibonacci_n_and_sn_prf : (Fibonacci_even_n_or_sn, Fibonacci_odd_n_or_sn) = SwappedIfOdd Parity_n (fibonacci n, fibonacci (S n))
 
-- examples
fib_with_parity_state_0 : FibWithParityState 0
fib_with_parity_state_0 = MkFibWithParityState Even 1 1 Refl Refl

fib_with_parity_state_1 : FibWithParityState 1
fib_with_parity_state_1 = MkFibWithParityState Odd 2 1 Refl Refl

fib_with_parity_state_3 : FibWithParityState 3
fib_with_parity_state_3 = MkFibWithParityState Odd 5 3 Refl Refl
-- end of examples

split_pair_equality: (x1, x2) = (y1, y2) -> (x1 = y1, x2 = y2)
split_pair_equality x1_x2_is_y1_y2 = (cong {f=fst} x1_x2_is_y1_y2, cong {f=snd} x1_x2_is_y1_y2)

next_fib_with_parity_state : FibWithParityState n -> FibWithParityState (S n)
next_fib_with_parity_state {n} (MkFibWithParityState Even fib_even fib_odd n_is_even fib_s_sn_prf) = 
  let e1 = the (ParityOf (S n) = Odd) $ rewrite n_is_even in Refl
      e2 = the ((fib_even, fib_odd) = (fibonacci n, fibonacci (S n))) $ fib_s_sn_prf
      (e3,e4) = the (fib_even = fibonacci n, fib_odd = fibonacci (S n)) $ split_pair_equality e2
      e5 = the (fib_even + fib_odd = fibonacci (S (S n))) $ rewrite e3 in rewrite e4 in Refl
      e6 = the ((fib_even + fib_odd, fib_odd) = (fibonacci (S (S n)), fibonacci (S n))) $ rewrite e5 in rewrite e4 in Refl
  in MkFibWithParityState Odd (fib_even + fib_odd) fib_odd e1 e6
next_fib_with_parity_state {n} (MkFibWithParityState Odd fib_even fib_odd n_is_odd fib_s_sn_prf) =
  let e1 = the (ParityOf (S n) = Even) $ rewrite n_is_odd in Refl
      e2 = the ((fib_even, fib_odd) = (fibonacci (S n), fibonacci n)) $ fib_s_sn_prf
      (e3,e4) = the (fib_even = fibonacci (S n), fib_odd = fibonacci n) $ split_pair_equality e2
      e5 = the (fib_odd + fib_even = fibonacci (S (S n))) $ rewrite e3 in rewrite e4 in Refl
      e6 = the ((fib_even, fib_odd + fib_even) = (fibonacci (S n), fibonacci (S (S n)))) $ rewrite e5 in rewrite e3 in Refl
  in MkFibWithParityState Even fib_even (fib_odd + fib_even) e1 e6
  
fib_with_parity_state_n : (n : Nat) -> FibWithParityState n
fib_with_parity_state_n Z = fib_with_parity_state_0
fib_with_parity_state_n (S k) = next_fib_with_parity_state $ fib_with_parity_state_n k

fib_n_by_parity : Parity -> FibWithParityState n -> Nat
fib_n_by_parity Even fib_state_n = Fibonacci_even_n_or_sn fib_state_n
fib_n_by_parity Odd fib_state_n = Fibonacci_odd_n_or_sn fib_state_n

fibonacci2 : (n : Nat) -> Nat
fibonacci2 n = fib_n_by_parity (ParityOf n) (fib_with_parity_state_n n)

fib2_eq_fib_for_n : (n : Nat) -> Type
fib2_eq_fib_for_n n = fibonacci2 n = fibonacci n

-- examples
fib2_eq_fib_for_3 : fib2_eq_fib_for_n 3
fib2_eq_fib_for_3 = Refl

fib2_eq_fib_for_8 : fib2_eq_fib_for_n 8
fib2_eq_fib_for_8 = Refl
-- end of examples

swapped_if_odd_when_even: (p = Even) -> SwappedIfOdd p (x,y) = (x,y)
swapped_if_odd_when_even p_is_even = rewrite p_is_even in Refl

swapped_if_odd_when_odd: (p = Odd) -> SwappedIfOdd p (x,y) = (y,x)
swapped_if_odd_when_odd p_is_odd = rewrite p_is_odd in Refl

fib_with_even_parity_state : (ParityOf n = Even) -> (fib_state : FibWithParityState n) -> Fibonacci_even_n_or_sn fib_state = fibonacci n
fib_with_even_parity_state {n} parity_of_n_is_even fib_state = 
  let e1 = Parity_n_prf fib_state
      e2 = the (Parity_n fib_state = Even) $ trans (sym e1) parity_of_n_is_even
      e3 = the ((Fibonacci_even_n_or_sn fib_state, Fibonacci_odd_n_or_sn fib_state) =
                 SwappedIfOdd (Parity_n fib_state) (fibonacci n, fibonacci (S n))) $  Fibonacci_n_and_sn_prf fib_state
      e4 = swapped_if_odd_when_even e2 {x=fibonacci n} {y=fibonacci (S n)}
      e5 = trans e3 e4
  in cong {f=fst} e5
  
fib_with_odd_parity_state : (ParityOf n = Odd) -> (fib_state : FibWithParityState n) -> Fibonacci_odd_n_or_sn fib_state = fibonacci n
fib_with_odd_parity_state {n} parity_of_n_is_odd fib_state = 
  let e1 = Parity_n_prf fib_state
      e2 = the (Parity_n fib_state = Odd) $ trans (sym e1) parity_of_n_is_odd
      e3 = the ((Fibonacci_even_n_or_sn fib_state, Fibonacci_odd_n_or_sn fib_state) =
                 SwappedIfOdd (Parity_n fib_state) (fibonacci n, fibonacci (S n))) $ Fibonacci_n_and_sn_prf fib_state
      e4 = swapped_if_odd_when_odd e2 {x=fibonacci n} {y=fibonacci (S n)}
      e5 = trans e3 e4
  in cong {f=snd} e5

fib2_eq_fib_given_p : (n : Nat) -> (p : Parity) -> ParityOf n = p -> fib2_eq_fib_for_n n
fib2_eq_fib_given_p n Even parity_of_n_is_p = 
  let e1 = fib_with_even_parity_state parity_of_n_is_p (fib_with_parity_state_n n)
  in rewrite parity_of_n_is_p in e1
fib2_eq_fib_given_p n Odd parity_of_n_is_p = 
  let e1 = fib_with_odd_parity_state parity_of_n_is_p (fib_with_parity_state_n n)
  in rewrite parity_of_n_is_p in e1

fib2_eq_fib: (n : Nat) -> fib2_eq_fib_for_n n
fib2_eq_fib n = fib2_eq_fib_given_p n (ParityOf n) Refl
