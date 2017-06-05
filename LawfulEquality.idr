module LawfulEquality

%default total

public export
is_reflexive : (t -> t -> Bool) -> Type
is_reflexive {t} rel = (x : t) -> rel x x = True

public export
is_symmetric : (t -> t -> Bool) -> Type
is_symmetric {t} rel = (x : t) -> (y : t) -> rel x y = rel y x

public export
is_transitive : (t -> t -> Bool) -> Type
is_transitive {t} rel = (x : t) -> (y : t) -> (z : t) -> rel x y = True -> rel x z = rel y z

public export
interface Eq t => LawfulEq t where
  eq_is_reflexive : is_reflexive {t} (==)
  eq_is_symmetric : is_symmetric {t} (==)
  eq_is_transitive : is_transitive {t} (==)

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
  
eq_implies_equality : {t : Type} -> (eq : t -> t -> Bool) -> Type
eq_implies_equality {t} eq = (x : t) -> (y : t) -> eq x y = True -> x = y

lemma : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> x = y -> rel x y = rel x x
lemma rel x y prf = rewrite prf in Refl

false_is_not_true: False = True -> Void
false_is_not_true Refl impossible

reflexive_eq_false_implies_not_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> rel x y = False -> x = y -> Void
reflexive_eq_false_implies_not_equal {t} {x} {y} rel is_refl_prf x_y_not_eq x_equals_y = 
  let x_eq_x = is_refl_prf x in
  let lemma2 = lemma rel x y x_equals_y in 
  let lemma3 = trans (sym x_y_not_eq) $ trans lemma2 x_eq_x in
    false_is_not_true lemma3

symmetric_eq_from_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> eq_implies_equality rel -> is_symmetric rel
symmetric_eq_from_equal {t} rel prf1 prf2 x y =
  ?hole

bool_eq_implies_equality : eq_implies_equality {t=Bool} (==)
bool_eq_implies_equality False False prf = Refl
bool_eq_implies_equality False True prf = prf
bool_eq_implies_equality True False prf = sym prf
bool_eq_implies_equality True True prf = Refl

