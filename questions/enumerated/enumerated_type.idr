import Data.Vect

%default total

data ABCD = A | B | C | D

interface FiniteType (t : Type) (size : Nat) | t where
  values : Vect size t
  toFin : t -> Fin size
  
nat_to_fin: Nat -> {max : Nat} -> Fin (S max)
nat_to_fin Z {max} = FZ
nat_to_fin (S k) {max = Z} = FZ
nat_to_fin (S k) {max = (S j)} = FS (nat_to_fin k)

FiniteType ABCD 4 where
  values = [A, B, C, D]
  toFin A = nat_to_fin 0
  toFin B = nat_to_fin 1
  toFin C = nat_to_fin 2
  toFin D = nat_to_fin 3

range : (n : Nat) -> Vect n (Fin n)
range Z = []
range (S k) = (FZ :: (map FS $ range k))


