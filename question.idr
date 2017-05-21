
%default total

data ABC = A | B | C

abc_2_nat : ABC -> Nat
abc_2_nat A = 1
abc_2_nat B = 1
abc_2_nat C = 2

data Projected_abc : Type where
  Project_abc : ABC -> Projected_abc
  
Projected_abc_equals : Projected_abc -> Projected_abc -> Bool
Projected_abc_equals (Project_abc x) (Project_abc y) = abc_2_nat x == abc_2_nat y

Eq Projected_abc where 
  (==) = Projected_abc_equals
  
data Projected : (t1 : Type) -> (t2 : Type) -> (p: t1 -> t2) -> Type
  where Project : t1 -> Projected t1 t2 p

Projected_equals : Eq t2 => Projected t1 t2 p -> Projected t1 t2 p -> Bool
Projected_equals (Project x) (Project y) = p x == p y

Projected_abc2 : Type
Projected_abc2 = Projected ABC Nat abc_2_nat

