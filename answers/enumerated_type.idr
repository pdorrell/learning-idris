import Data.Fin
import Data.Vect

%default total

-- the FiniteType interface, representing a type with a finite number of possible values

interface FiniteType (t : Type) (size : Nat) | t where
  values : Vect size t
  toFin : t -> Fin size
  fromFin : Fin size -> t
  
  fromFin n = index n values
  
eq_from_fin : FiniteType t size => t -> t -> Bool
eq_from_fin x y = toFin x == toFin y

nat_to_fin: Nat -> {max : Nat} -> Fin (S max)
nat_to_fin Z {max} = FZ
nat_to_fin (S k) {max = Z} = FZ
nat_to_fin (S k) {max = (S j)} = FS (nat_to_fin k)

data MyType
    = One | Two | Three | Four | Five | Six | Seven | Eight | Nine | Ten

FiniteType MyType 10 where
  values = [One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten]
  toFin One   = nat_to_fin 0
  toFin Two   = nat_to_fin 1
  toFin Three = nat_to_fin 2
  toFin Four  = nat_to_fin 3
  toFin Five  = nat_to_fin 4
  toFin Six   = nat_to_fin 5
  toFin Seven = nat_to_fin 6
  toFin Eight = nat_to_fin 7
  toFin Nine  = nat_to_fin 8
  toFin Ten   = nat_to_fin 9
  
Eq MyType where
  (==) = eq_from_fin

four_eq_four : Four == Four = True
four_eq_four = Refl

four_not_eq_seven : Four == Seven = False
four_not_eq_seven = Refl

interface FiniteType t size => VerifiedFiniteType t (size : Nat) | t where
  toAndFromFin : (x : t) -> the t (fromFin (toFin x)) = x
  fromAndToFin : (y : Fin size) -> toFin (the t (fromFin y)) = y
