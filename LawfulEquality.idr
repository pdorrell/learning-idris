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
  
implies_equality : {t : Type} -> (eq : t -> t -> Bool) -> Type
implies_equality {t} eq = (x : t) -> (y : t) -> eq x y = True -> x = y

false_is_not_true: False = True -> Void
false_is_not_true Refl impossible

reflexive_rel_false_implies_not_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> rel x y = False -> x = y -> Void
reflexive_rel_false_implies_not_equal {t} {x} {y} rel is_refl_prf x_y_not_eq x_is_y = 
  let x_eq_x = is_refl_prf x in
  let lemma2 = lemma rel x y x_is_y in 
  let lemma3 = trans (sym x_y_not_eq) $ trans lemma2 x_eq_x in
    false_is_not_true lemma3 where
      lemma : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> x = y -> rel x y = rel x x
      lemma rel x y prf = rewrite prf in Refl

lemma_t : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> is_reflexive rel -> implies_equality rel -> rel x y = True -> rel x y = rel y x
lemma_t rel x y is_reflexive_rel implies_equality_rel relxy_true = 
  let lemma2 = implies_equality_rel x y relxy_true in
    rewrite lemma2 in Refl 
    
inequality_symmetric : (x : t) -> (y : t) -> ((x = y) -> Void) -> ((y = x) -> Void)
inequality_symmetric x y x_not_equal_to_y y_is_x = x_not_equal_to_y $ sym y_is_x

implies_equality_converse: {t : Type} -> (rel : t -> t -> Bool) -> implies_equality rel -> ((x = y) -> Void) -> rel x y = value -> value = False
implies_equality_converse {x=x} {y=y} {value} rel implies_equality_rel x_is_not_y rel_x_y_value = 
  let rel_x_y = rel x y in
  case value of
    True => let x_is_y = implies_equality_rel x y rel_x_y_value in 
            let void_value = x_is_not_y x_is_y in
              void void_value
    False => Refl
    
has_value_dpair : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> (value: Bool ** rel x y = value)
has_value_dpair rel x y = (rel x y ** Refl)

lemma_f : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> is_reflexive rel -> implies_equality rel -> rel x y = False -> rel x y = rel y x
lemma_f rel x y is_reflexive_rel implies_equality_rel rel_x_y_is_false = 
  let x_is_not_y = reflexive_rel_false_implies_not_equal {x=x} {y=y} rel is_reflexive_rel rel_x_y_is_false in
  let y_is_not_x = inequality_symmetric x y x_is_not_y in
  let value_is_false = implies_equality_converse rel implies_equality_rel y_is_not_x in
  let rel_has_value_dpair = has_value_dpair rel y x in
  let rel_has_value = snd rel_has_value_dpair in
  let rel_y_x_is_false = value_is_false rel_has_value in 
  trans rel_x_y_is_false $ sym rel_y_x_is_false
  
elim_t_or_f_rel: {prop: Type} -> (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> (value : Bool ** rel x y = value) -> (rel x y = False -> prop, rel x y = True -> prop) -> prop
elim_t_or_f_rel {prop = prop} rel x y (False ** rel_x_y_is_value) true_or_false_implies_prop = fst true_or_false_implies_prop $ rel_x_y_is_value
elim_t_or_f_rel {prop = prop} rel x y (True ** rel_x_y_is_value) true_or_false_implies_prop = snd true_or_false_implies_prop $ rel_x_y_is_value

lemma : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> is_reflexive rel -> implies_equality rel -> rel x y = rel y x
lemma rel x y is_reflexive_rel implies_equality_rel = 
  let rel_has_value_dpair = has_value_dpair rel x y in
  let t_hyp = lemma_t rel x y is_reflexive_rel implies_equality_rel in
  let f_hyp = lemma_f rel x y is_reflexive_rel implies_equality_rel in
  elim_t_or_f_rel {prop=(rel x y = rel y x)} rel x y rel_has_value_dpair (f_hyp, t_hyp)

symmetric_eq_from_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> implies_equality rel -> is_symmetric rel
symmetric_eq_from_equal {t} rel is_reflexive_rel implies_equality_rel x y =
  lemma {t} rel x y is_reflexive_rel implies_equality_rel

bool_eq_implies_equality : implies_equality {t=Bool} (==)
bool_eq_implies_equality False False prf = Refl
bool_eq_implies_equality False True prf = prf
bool_eq_implies_equality True False prf = sym prf
bool_eq_implies_equality True True prf = Refl

bool_eq_is_symmetric : (x : Bool) -> (y : Bool) -> x == y = y == x
bool_eq_is_symmetric = symmetric_eq_from_equal (==) bool_equality_lemmas.reflexive bool_eq_implies_equality
