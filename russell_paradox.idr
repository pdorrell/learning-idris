%default total

data Set : Type where
  MkSet : (x : Type) -> (x -> Set) -> Set

IsMemberOf : Set -> Set -> Type
IsMemberOf a (MkSet x f) = (x_value: x ** (a = f x_value))

IsNotMemberOf : Set -> Set -> Type
IsNotMemberOf a b = (IsMemberOf a b) -> Void

RussellsSet : Set
RussellsSet = MkSet (x ** IsNotMemberOf x x) fst

lemma1 : {x : Set} -> (IsMemberOf x RussellsSet) -> IsNotMemberOf x x
lemma1 {x} x_in_russell = ?hole
