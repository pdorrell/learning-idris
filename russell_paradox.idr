%default total

-- Adapted from Agda code in http://liamoc.net/posts/2015-09-10-girards-paradox.html

data Set : Type where
  MkSet : (x : Type) -> (x -> Set) -> Set

DepPairType : (x : Type) -> (f: x -> Type) -> Type
DepPairType x f = (x1 : x ** f x1)

DepPair : {x : Type} -> {f : x -> Type} -> (x1 : x) -> (y : f x1) -> DepPairType x f
DepPair {x} {f} x1 y = (x1 ** y)

DepPairFst : {x : Type} -> {f : x -> Type} -> DepPairType x f -> x
DepPairFst {x} {f} p = fst p

DepPairSnd : {x : Type} -> {f : x -> Type} -> (p : DepPairType x f) -> (f (fst p))
DepPairSnd p = snd p

IsMemberOf : Set -> Set -> Type
IsMemberOf a (MkSet x f) = DepPairType x (\x_value => (a = f x_value))

IsNotMemberOf : Set -> Set -> Type
IsNotMemberOf a b = (IsMemberOf a b) -> Void

RussellsSet : Set
RussellsSet = MkSet (DepPairType Set (\x => IsNotMemberOf x x)) DepPairFst

x_in_rs_implies_x_not_in_x : {x : Set} -> (IsMemberOf x RussellsSet) -> IsNotMemberOf x x
x_in_rs_implies_x_not_in_x {x} x_in_russell = 
  let x1 = DepPairFst x_in_russell
      x1a = DepPairFst x1
      x1b = the (IsMemberOf x1a x1a -> Void) $  DepPairSnd x1
      x2 = the (x = x1a) $ DepPairSnd x_in_russell
  in rewrite x2 in x1b
  
x_not_in_x_implies_x_in_rs : {set : Set} -> IsNotMemberOf set set -> (IsMemberOf set RussellsSet)
x_not_in_x_implies_x_in_rs {set} set_not_in_set = 
  let set_where_set_not_in_set = the (DepPairType Set (\s => IsNotMemberOf s s)) $ (DepPair set set_not_in_set)
      result = the (DepPairType (DepPairType Set (\x1 => IsNotMemberOf x1 x1)) (\x2 => set = DepPairFst x2)) 
                        (DepPair set_where_set_not_in_set (the (set = DepPairFst set_where_set_not_in_set) Refl) )
  in result

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
