
interface Computer a where
  compute : a -> Nat
  
[double] Computer Nat where
  compute n = n + n

[increment] Computer Nat where
  compute n = S n

compute_from_compute_param : Nat -> Computer Nat -> Nat
compute_from_compute_param k computer = compute k

compute_by_doubling : Nat -> Nat
compute_by_doubling k = compute_from_compute_param k double

compute_by_incrementing : Nat -> Nat
compute_by_incrementing k = compute_from_compute_param k increment

compute_from_two_compute_params : Nat -> Computer Nat -> Computer Nat -> Nat
compute_from_two_compute_params k computer1 computer2 = compute k

compute_by_doubling_or_maybe_incrementing : Nat -> Nat
compute_by_doubling_or_maybe_incrementing k = compute_from_two_compute_params k double increment

compute_by_doubling_or_maybe_incrementing_4 : compute_by_doubling_or_maybe_incrementing 4 = 5
compute_by_doubling_or_maybe_incrementing_4 = Refl

compute_by_incrementing_or_maybe_doubling : Nat -> Nat
compute_by_incrementing_or_maybe_doubling k = compute_from_two_compute_params k increment double

compute_by_incrementing_or_maybe_doubling_4 : compute_by_incrementing_or_maybe_doubling 4 = 8
compute_by_incrementing_or_maybe_doubling_4 = Refl
