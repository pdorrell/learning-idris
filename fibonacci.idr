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

fib_state_n : (n : Nat) -> FibState n
fib_state_n Z = fib_state_0
fib_state_n (S k) = next_fib_state $ fib_state_n k

fibonacci2 : Nat -> Nat
fibonacci2 Z = 1
fibonacci2 (S k) = y $ fib_state_n k

lemma3 : {fsn : FibState n} -> y (next_fib_state fsn) = x fsn + y fsn
lemma3 {fsn} = 
  let MkFibState x y x_is_fn y_is_fn1 = fsn
  in Refl

lemma2 : y (next_fib_state (fib_state_n n)) = x (fib_state_n n) + y (fib_state_n n)
lemma2 {n} = lemma3 {fsn=fib_state_n n}

fib_eq_fib2_lemma : fibonacci (S n) = fibonacci2 (S n) -> fibonacci (S (S n)) = fibonacci2 (S (S n))
fib_eq_fib2_lemma {n} fib_sn_is_fib2_sn = 
  let e1 = the (fibonacci2 (S n) = y $ fib_state_n n) $ Refl
      e2 = the (fibonacci (S n) = y (fib_state_n n)) $ trans fib_sn_is_fib2_sn e1
  in ?hole


fib_eq_fib2_induct : fibonacci n = fibonacci2 n -> fibonacci (S n) = fibonacci2 (S n)
fib_eq_fib2_induct {n = Z} induct_hyp = Refl
fib_eq_fib2_induct {n = S k} induct_hyp = fib_eq_fib2_lemma induct_hyp

fib_eq_fib2 : (n: Nat) -> fibonacci n = fibonacci2 n
fib_eq_fib2 Z = Refl
fib_eq_fib2 (S k) = fib_eq_fib2_induct $ fib_eq_fib2 k
 


