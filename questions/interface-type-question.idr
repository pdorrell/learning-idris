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

example3 : (a : Type) -> Eq a -> Eq a -> (x : a) -> (y : a) -> Type
example3 a eqa1 eqa2 x y = 
  --let fun = (==) in
  let value = x == y in 
  let equality_type = x == y = True in
  ?hole

example4 : (a : Type) -> Eq a -> (x : a) -> (y : a) -> Type
example4 a eqa1 x y = 
  let fun = (==) in
  let value = x == y in 
  let equality_type = x == y = True in
  ?hole2


--x == y = True
