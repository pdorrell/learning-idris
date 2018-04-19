import Data.Vect

%default total

range : (n : Nat) -> Vect n (Fin n)
range Z = []
range (S k) = (FZ :: (map FS $ range k))

interface EnumeratedType (t : Type) (size : Nat) | t where
  values : Vect size t
  toFin : t -> Fin size
  values_match_toFin : map toFin values = range size
  
fromFin : (EnumeratedType t size) => Fin size -> t
fromFin x = index x values

data MyType = One | Two | Three | Four | Five | Six | Seven | Eight | Nine | Ten

EnumeratedType MyType 10 where
  values = [One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten]
  toFin One   = 0
  toFin Two   = 1
  toFin Three = 2
  toFin Four  = 3
  toFin Five  = 4
  toFin Six   = 5
  toFin Seven = 6
  toFin Eight = 7
  toFin Nine  = 8
  toFin Ten   = 9
  values_match_toFin = Refl

eq_from_fin : (EnumeratedType t size) => t -> t -> Bool
eq_from_fin x y = toFin x == toFin y

Eq MyType where
  (==) = eq_from_fin

Three_eq_Three : Three == Three = True
Three_eq_Three = Refl

Four_not_eq_Seven : Four == Seven = False
Four_not_eq_Seven = Refl
