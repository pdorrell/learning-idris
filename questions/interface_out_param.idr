import Data.Vect

%default total

data ABCD = A | B | C | D

interface FiniteType t where
  size : Nat
  values : Vect size t
  toFin : t -> Fin size
  fromFin : Fin size -> t

FiniteType ABCD where
  size = the Nat 4
  values = [A, B, C, D]
  toFin A = FZ
  toFin B = (FS FZ)
  toFin C = (FS (FS FZ))
  toFin D = (FS (FS (FS FZ)))
  fromFin n = index n values
  
test : (x : ABCD) -> (y : ABCD) -> Type
test x y = toFin x = toFin y


--test2 : (x : ABCD) -> (y : ABCD) -> Type
--test2 x y = fromFin (toFin x) = fromFin (toFin y)
