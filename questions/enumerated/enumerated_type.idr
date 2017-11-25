import Data.Vect

%default total

data ABCD = A | B | C | D

interface FiniteType (t : Type) (size : Nat) | t where
  values : Vect size t
  toFin : t -> Fin size
  
FiniteType ABCD 4 where
  values = [A, B, C, D]
  toFin A = 0
  toFin B = 1
  toFin C = 2
  toFin D = 3

range : (n : Nat) -> Vect n (Fin n)
range Z = []
range (S k) = (FZ :: (map FS $ range k))

interface FiniteType t size => VerifiedFiniteType t (size : Nat) | t where
  toAndFromFin : map toFin values = range size
