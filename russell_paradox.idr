%default total

-- Adapted from Agda code in http://liamoc.net/posts/2015-09-10-girards-paradox.html

data Set : Type where
  MkSet : (x : Type) -> (x -> Set) -> Set

IsMemberOf : Set -> Set -> Type
IsMemberOf a (MkSet x f) = (x_value: x ** (a = f x_value))

IsNotMemberOf : Set -> Set -> Type
IsNotMemberOf a b = (IsMemberOf a b) -> Void

RussellsSet : Set
RussellsSet = MkSet (x : Set ** IsNotMemberOf x x) fst

x_in_rs_implies_x_not_in_x : {x : Set} -> (IsMemberOf x RussellsSet) -> IsNotMemberOf x x
x_in_rs_implies_x_not_in_x {x} x_in_russell = 
  let ((x ** x_is_not_member_of_x) ** Refl) = x_in_russell
  in x_is_not_member_of_x
  
x_not_in_x_implies_x_in_rs : {x : Set} -> IsNotMemberOf x x -> (IsMemberOf x RussellsSet)
x_not_in_x_implies_x_in_rs {x} x_not_in_x = ((x ** x_not_in_x) ** Refl)

rs_in_rs_implies_rs_not_in_rs : (IsMemberOf RussellsSet RussellsSet) -> (IsNotMemberOf RussellsSet RussellsSet)
rs_in_rs_implies_rs_not_in_rs rs_in_itself = x_in_rs_implies_x_not_in_x rs_in_itself

rs_not_in_rs : (IsMemberOf RussellsSet RussellsSet) -> Void
rs_not_in_rs rs_in_itself = 
  let rs_not_in_itself = rs_in_rs_implies_rs_not_in_rs rs_in_itself
  in rs_not_in_itself rs_in_itself

rs_in_rs : IsMemberOf RussellsSet RussellsSet
rs_in_rs = x_not_in_x_implies_x_in_rs rs_not_in_rs

russells_paradox : Void
russells_paradox = rs_not_in_rs rs_in_rs
