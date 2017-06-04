%default total

example1: Eq a => (x : a) -> (y : a) -> Type
example1 {a} x y = ?example1_rhs

example1b: Eq a => (x : a) -> (y : a) -> Type
example1b {a} x y = x == y = True

example2: (a : Type) -> Eq a -> (x : a) -> (y : a) -> Type
example2 a eqa x y = ?example2_rhs

example2b: (a : Type) -> Eq a -> (x : a) -> (y : a) -> Type
example2b a eqa x y = x == y = True

[eq_nat] Eq Nat where
  (==) Z Z = True
  (==) Z (S k) = False
  (==) (S k) Z = False
  (==) (S k) (S j) = k == j

example_of_example2 : Type
example_of_example2 = example2 Nat eq_nat 3 3

eq_example: Eq Nat
eq_example = eq_nat
