%default total

example1: (a : Type) -> Eq a -> (x : a) -> (y : a) -> Type
example1 a eqa x y = ?example1_rhs

example1b: (a : Type) -> Eq a -> (x : a) -> (y : a) -> Type
example1b a eqa x y = x == y = True

example2: Eq a => (x : a) -> (y : a) -> Type
example2 {a} x y = ?example2_rhs

example2b: Eq a => (x : a) -> (y : a) -> Type
example2b {a} x y = x == y = True

eq_nat : Eq Nat
eq_nat = ?eq_nat_rhs

example_of_example1 : Type
example_of_example1 = example1 Nat eq_nat 3 3
