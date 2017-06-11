interface Computer a where
  compute : a -> Nat
  
[DoubleIt] Computer Nat where
  compute n = n + n

[IncrementIt] Computer Nat where
  compute n = S n

compute_from_two_compute_params : Nat -> Computer Nat -> Computer Nat -> Nat
compute_from_two_compute_params k computer1 computer2 = compute k

-- Apparently the second 'Computer Nat' param determines the result ...
example_compute_on_4 : compute_from_two_compute_params 4 DoubleIt IncrementIt = 5
example_compute_on_4 = Refl
