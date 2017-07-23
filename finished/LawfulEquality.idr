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
is_transitive_from_right : (t -> t -> Bool) -> Type
is_transitive_from_right {t} rel = (x : t) -> (y : t) -> (z : t) -> rel x y = True -> rel z x = rel z y

-- If we have is_symmetric & is_transitive in LawfulEq, we don't have to include is_transitive_from_right, 
-- because it is implied by the first two ...
is_transitive_from_right_lemma : (rel : t -> t -> Bool) -> is_symmetric rel -> is_transitive rel -> is_transitive_from_right rel
is_transitive_from_right_lemma {t} rel is_symmetric_rel is_transitive_rel x y z rel_x_y_is_true = 
  let rel_z_x_is_rel_x_z = is_symmetric_rel {x=z} {y=x} in
  let rel_y_z_is_rel_z_y = is_symmetric_rel {x=y} {y=z} in
  let trans_rel_x_y_z = is_transitive_rel {x} {y} {z} rel_x_y_is_true in
  trans rel_z_x_is_rel_x_z $ trans trans_rel_x_y_z rel_y_z_is_rel_z_y

public export
interface Eq t => LawfulEq t where
  eq_is_reflexive : is_reflexive {t} (==)
  eq_is_symmetric : is_symmetric {t} (==)
  eq_is_transitive : is_transitive {t} (==)
  
lawful_eq_is_transitive_from_right: LawfulEq t => is_transitive_from_right {t} (==)
lawful_eq_is_transitive_from_right {t} = is_transitive_from_right_lemma (==) eq_is_symmetric eq_is_transitive

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
  
