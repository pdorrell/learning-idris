
-- This is a non-total function on Nat, defined only for Z
is_zero: (n : Nat) -> Bool
is_zero Z = True

-- If I have a proof that is_zero n = True, then n must be Z, by case-splitting on the non-total definition of is_zero.
is_zero_if_zero : (n : Nat) -> is_zero n = True -> n = Z
is_zero_if_zero Z prf = Refl

-- I don't think there is any way to prove this ...
is_zero_result_must_be_true : is_zero n = value -> value = True
is_zero_result_must_be_true Refl = ?is_zero_result_must_be_true_rhs_1

-- messing round with application as an abstraction ...
total
applicator: (f : t1 -> t2) -> (x : t1) -> t2
applicator f x = f x

is_zero_applicator: (n : Nat) -> Bool
is_zero_applicator = applicator is_zero

