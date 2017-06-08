module EqFromEquality

%default total

-- Proof: if an instance Eq corresponds to intensional equality, then (==) is symmetric

is_reflexive : (t -> t -> Bool) -> Type
is_reflexive {t} rel = (x : t) -> rel x x = True

is_symmetric : (t -> t -> Bool) -> Type
is_symmetric {t} rel = (x : t) -> (y : t) -> rel x y = rel y x

implies_equality : {t : Type} -> (rel : t -> t -> Bool) -> Type
implies_equality {t} rel = (x : t) -> (y : t) -> rel x y = True -> x = y

false_is_not_true: False = True -> Void
false_is_not_true Refl impossible

contrapositive: (prop1 -> prop2) -> ((prop2 -> Void) -> (prop1 -> Void))
contrapositive prop1_implies_prop2 not_prop2 prop1_prf = not_prop2 $ prop1_implies_prop2 $ prop1_prf

has_value_dpair : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> (value: Bool ** rel x y = value)
has_value_dpair rel x y = (rel x y ** Refl)

rel_x_y_is_not_true_implies_its_false : (rel : t -> t -> Bool) -> ((rel x y = True) -> Void) -> rel x y = False
rel_x_y_is_not_true_implies_its_false rel {x} {y} rel_x_y_is_not_true with (has_value_dpair rel x y)
  | (True ** rel_x_y_is_value) = void $ rel_x_y_is_not_true rel_x_y_is_value
  | (False ** rel_x_y_is_value) = rel_x_y_is_value
    
reflexive_rel_false_implies_not_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> rel x y = False -> x = y -> Void
reflexive_rel_false_implies_not_equal {t} {x} {y} rel is_reflexive_rel rel_x_y_is_false x_is_y = 
  let rel_x_x_is_true = is_reflexive_rel x in
  let rel_x_y_is_rel_x_x = cong {f= \z => rel x z} $ sym x_is_y in 
  let false_is_true = trans (sym rel_x_y_is_false) $ trans rel_x_y_is_rel_x_x rel_x_x_is_true in
    false_is_not_true false_is_true
    
lemma_t : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> is_reflexive rel -> implies_equality rel -> rel x y = True -> rel x y = rel y x
lemma_t rel x y is_reflexive_rel implies_equality_rel rel_x_y_is_true = 
  let x_is_y = implies_equality_rel x y rel_x_y_is_true in
  rewrite x_is_y in Refl
    
inequality_symmetric : (x : t) -> (y : t) -> ((x = y) -> Void) -> ((y = x) -> Void)
inequality_symmetric x y x_is_not_y y_is_x = x_is_not_y $ sym y_is_x

implies_equality_contrapositive: {t : Type} -> (rel : t -> t -> Bool) -> implies_equality rel -> ((x = y) -> Void) -> rel x y = False
implies_equality_contrapositive rel implies_equality_rel {x} {y} x_is_not_y = 
  let rel_x_y_is_not_true = (contrapositive $ implies_equality_rel x y) x_is_not_y in
  rel_x_y_is_not_true_implies_its_false rel rel_x_y_is_not_true

lemma_f : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> is_reflexive rel -> implies_equality rel -> rel x y = False -> rel x y = rel y x
lemma_f rel x y is_reflexive_rel implies_equality_rel rel_x_y_is_false = 
  let x_is_not_y = reflexive_rel_false_implies_not_equal {x} {y} rel is_reflexive_rel rel_x_y_is_false in
  let y_is_not_x = inequality_symmetric x y x_is_not_y in
  let rel_y_x_is_false = implies_equality_contrapositive rel implies_equality_rel y_is_not_x in
  trans rel_x_y_is_false $ sym rel_y_x_is_false
  
elim_t_or_f_rel: {prop: Type} -> (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> (rel x y = False -> prop, rel x y = True -> prop) -> prop
elim_t_or_f_rel {prop} rel x y t_or_f_implies_prop with (has_value_dpair rel x y)
  | (False ** rel_x_y_is_value) = fst t_or_f_implies_prop $ rel_x_y_is_value
  | (True ** rel_x_y_is_value) = snd t_or_f_implies_prop $ rel_x_y_is_value

lemma : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> is_reflexive rel -> implies_equality rel -> rel x y = rel y x
lemma rel x y is_reflexive_rel implies_equality_rel = 
  let t_hyp = lemma_t rel x y is_reflexive_rel implies_equality_rel in
  let f_hyp = lemma_f rel x y is_reflexive_rel implies_equality_rel in
  elim_t_or_f_rel {prop=(rel x y = rel y x)} rel x y (f_hyp, t_hyp)

symmetric_eq_from_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> implies_equality rel -> is_symmetric rel
symmetric_eq_from_equal {t} rel is_reflexive_rel implies_equality_rel x y =
  lemma {t} rel x y is_reflexive_rel implies_equality_rel
  

-- an example involving Eq Bool

bool_is_reflexive : (x : Bool) -> x == x = True
bool_is_reflexive False = Refl
bool_is_reflexive True = Refl

bool_eq_implies_equality : implies_equality {t=Bool} (==)
bool_eq_implies_equality False False prf = Refl
bool_eq_implies_equality False True prf = prf
bool_eq_implies_equality True False prf = sym prf
bool_eq_implies_equality True True prf = Refl

bool_eq_is_symmetric : (x : Bool) -> (y : Bool) -> x == y = y == x
bool_eq_is_symmetric = symmetric_eq_from_equal (==) bool_is_reflexive bool_eq_implies_equality
