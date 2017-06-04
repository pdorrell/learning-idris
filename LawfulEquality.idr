module LawfulEquality

%default total

public export
interface Eq t => LawfulEq t where
  eq_is_reflexive : (x : t) -> x == x = True
  eq_is_symmetric : (x : t) -> (y : t) -> x == y = y == x
  eq_is_transitive : (x : t) -> (y : t) -> (z : t) -> x == y = True -> x == z = y == z

-- some useful implementations ...  

namespace bool_equality_lemmas
  
  reflexive : (x : Bool) -> x == x = True
  reflexive False = Refl
  reflexive True = Refl

  symmetric : (x : Bool) -> (y : Bool) -> x == y = y == x
  symmetric False False = Refl
  symmetric False True = Refl
  symmetric True False = Refl
  symmetric True True = Refl

  transitive : (x : Bool) -> (y : Bool) -> (z : Bool) -> x == y = True -> x == z = y == z
  transitive False False z Refl = Refl
  transitive False True _ Refl impossible
  transitive True False _ Refl impossible
  transitive True True z Refl = Refl

public export
LawfulEq Bool where
  eq_is_reflexive = bool_equality_lemmas.reflexive
  eq_is_symmetric = bool_equality_lemmas.symmetric
  eq_is_transitive = bool_equality_lemmas.transitive
  
--eq_implies_equality : (eqa : Eq a) => {a : Type} -> Type
--eq_implies_equality a = (x : a) -> (y : a) -> x==y = True -> x = y

eq_implies_equality : {a : Type} -> (eq : a -> a -> Bool) -> Type
eq_implies_equality {a} eq = (x : a) -> (y : a) -> eq x y = True -> x = y

bool_eq : Bool -> Bool -> Bool
bool_eq x y = x == y

bool_eq_implies_equality : eq_implies_equality {a=Bool} LawfulEquality.bool_eq
bool_eq_implies_equality False False prf = Refl
bool_eq_implies_equality False True prf = prf
bool_eq_implies_equality True False prf = sym prf
bool_eq_implies_equality True True prf = Refl
