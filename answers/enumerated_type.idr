import Data.Fin
import Data.Vect

%default total

-- the FiniteType interface, representing a type with a finite number of possible values

interface FiniteType t where
  size : Nat
  values : Vect size t
  toFin : t -> Fin size
  fromFin : Fin size -> t
  
  fromFin n = index n values
  
eq_from_fin : FiniteType t => t -> t -> Bool
eq_from_fin x y = toFin x == toFin y

data MyType
    = One | Two | Three | Four | Five | Six | Seven | Eight | Nine | Ten

FiniteType MyType where
  size = the Nat 10
  values = [One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten]
  toFin One = FZ
  toFin Two = (FS FZ)
  toFin Three = (FS (FS FZ))
  toFin Four = (FS (FS (FS FZ)))
  toFin Five = (FS (FS (FS (FS FZ))))
  toFin Six = (FS (FS (FS (FS (FS FZ)))))
  toFin Seven = (FS (FS (FS (FS (FS (FS FZ))))))
  toFin Eight = (FS (FS (FS (FS (FS (FS (FS FZ)))))))
  toFin Nine = (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))
  toFin Ten = (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))
  
Eq MyType where
  (==) = eq_from_fin

four_eq_four : Four == Four = True
four_eq_four = Refl

four_not_eq_seven : Four == Seven = False
four_not_eq_seven = Refl
