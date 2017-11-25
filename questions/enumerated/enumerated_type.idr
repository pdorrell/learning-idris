import Data.Vect

%default total

range : (n : Nat) -> Vect n (Fin n)
range Z = []
range (S k) = (FZ :: (map FS $ range k))

interface FiniteType (t : Type) (size : Nat) | t where
  values : Vect size t
  toFin : t -> Fin size
  values_match_toFin : map toFin values = range size
  
fromFin : (FiniteType t size) => Fin size -> t
fromFin x = index x values

data ABCD = A | B | C | D

FiniteType ABCD 4 where
  values = [A, B, C, D]
  toFin A = 0
  toFin B = 1
  toFin C = 2
  toFin D = 3
  values_match_toFin = Refl

eq_from_fin : (FiniteType t size) => t -> t -> Bool
eq_from_fin x y = toFin x == toFin y

Eq ABCD where
  (==) = eq_from_fin

A_eq_A : A == A = True
A_eq_A = Refl

A_not_eq_C : A == C = False
A_not_eq_C = Refl
