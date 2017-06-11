module EqFromEquality

%default total

-- Proof: if an instance Eq corresponds to intensional equality, then (==) is symmetric
-- In the following, 'rel' is a relationship between elements in a type t, represented
-- by a total function that returns a boolean value.

-- Reflexive: x relates to x
is_reflexive : (t -> t -> Bool) -> Type
is_reflexive {t} rel = (x : t) -> rel x x = True

-- Symmetric: x relates to y iff y relates to x
is_symmetric : (t -> t -> Bool) -> Type
is_symmetric {t} rel = (x : t) -> (y : t) -> rel x y = rel y x

-- Transitive: if x relates to y, x relates to z iff y relates to z.
is_transitive : (t -> t -> Bool) -> Type
is_transitive {t} rel = (x : t) -> (y : t) -> (z : t) -> rel x y = True -> rel x z = rel y z

-- A relationship implies (intensional) equality if x relates to y only if x = y.
-- Not all 'equality' relationships we want to consider will have this property,
-- but in cases where they do, we should be able to immediately prove certain
-- properties about such a relationship.
rel_true_implies_equality : {t : Type} -> (rel : t -> t -> Bool) -> Type
rel_true_implies_equality {t} rel = (x : t) -> (y : t) -> rel x y = True -> x = y

rel_false_implies_inequality : {t : Type} -> (rel : t -> t -> Bool) -> Type
rel_false_implies_inequality {t} rel = (x : t) -> (y : t) -> rel x y = False -> (x = y -> Void)


-- Re-expressing is_reflexive as a function of two values x & y, given a proof that they are equal
reflexive_x_is_y_lemma: {rel : t -> t -> Bool} -> is_reflexive rel -> (x : t) -> (y : t) -> x = y -> rel x y = True
reflexive_x_is_y_lemma {rel} is_reflexive_rel y y Refl = is_reflexive_rel y

-- (constructive) law of contrapositive
contrapositive: (prop1 -> prop2) -> (Not prop2 -> Not prop1)
contrapositive prop1_implies_prop2 not_prop2 prop1_prf = not_prop2 $ prop1_implies_prop2 $ prop1_prf

-- for rel x y, provide both the computed value, and the proposition that it is equal to the value (as a dependent pair)
has_value_dpair : (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> (value: Bool ** rel x y = value)
has_value_dpair rel x y = (rel x y ** Refl)

-- Lemma: rel x y not equal to True implies that it is equal to False
rel_x_y_is_not_true_implies_its_false : (rel : t -> t -> Bool) -> (rel x y = True -> Void) -> rel x y = False
rel_x_y_is_not_true_implies_its_false rel {x} {y} rel_x_y_is_not_true with (has_value_dpair rel x y)
  | (True ** rel_x_y_is_value) = void $ rel_x_y_is_not_true rel_x_y_is_value
  | (False ** rel_x_y_is_value) = rel_x_y_is_value
  
-- Lemma: rel x y equal to False implies that it is not equal to True
rel_x_y_is_false_implies_its_not_true : (rel : t -> t -> Bool) -> rel x y = False -> (rel x y = True -> Void)
rel_x_y_is_false_implies_its_not_true rel rel_x_y_is_false rel_x_y_is_true = 
  let false_is_true = trans (sym rel_x_y_is_false) rel_x_y_is_true in 
    trueNotFalse $ sym false_is_true

-- For a reflexive relationship, rel x y not equal to True implies x and y are not equal
reflexive_rel_not_true_implies_not_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> (rel x y = True -> Void) -> x = y -> Void
reflexive_rel_not_true_implies_not_equal {x} {y} rel is_reflexive_rel rel_not_true = 
  let x_is_y_lemma = reflexive_x_is_y_lemma {rel} is_reflexive_rel x y in 
  let x_is_y_lemma_contra = contrapositive x_is_y_lemma in
    x_is_y_lemma_contra rel_not_true

-- For a reflexive relationship, rel x y equal to False implies x and y are not equal
reflexive_rel_false_implies_not_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> rel x y = False -> x = y -> Void
reflexive_rel_false_implies_not_equal {t} {x} {y} rel is_reflexive_rel rel_x_y_is_false = 
  let rel_x_y_is_not_true = rel_x_y_is_false_implies_its_not_true {x} {y} rel rel_x_y_is_false in
    reflexive_rel_not_true_implies_not_equal {x} {y} rel is_reflexive_rel rel_x_y_is_not_true
    
-- Lemma: the proof that a reflexive equality relationship where equality implies intensional equality 
-- is symmetric, in the case there the equality value is True.
lemma_t : (rel : t -> t -> Bool) -> is_reflexive rel -> rel_true_implies_equality rel -> (x : t) -> (y : t) -> rel x y = True -> rel x y = rel y x
lemma_t rel is_reflexive_rel rel_true_implies_equality_rel x y rel_x_y_is_true = 
  let x_is_y = rel_true_implies_equality_rel x y rel_x_y_is_true in
    rewrite x_is_y in Refl
    
-- Given an equality relationship were equality implies intensional equality,
-- the contrapositive is that intensional inequality implies not equal.
rel_true_implies_equality_contrapositive: {t : Type} -> (rel : t -> t -> Bool) -> rel_true_implies_equality rel -> ((x = y) -> Void) -> rel x y = False
rel_true_implies_equality_contrapositive rel rel_true_implies_equality_rel {x} {y} x_is_not_y = 
  let rel_x_y_is_not_true = (contrapositive $ rel_true_implies_equality_rel x y) x_is_not_y in
    rel_x_y_is_not_true_implies_its_false rel rel_x_y_is_not_true

-- Lemma: the proof that a reflexive equality relationship where equality implies intensional equality 
-- is symmetric, in the case there the equality value is False.
lemma_f : (rel : t -> t -> Bool) -> is_reflexive rel -> rel_true_implies_equality rel -> (x : t) -> (y : t) -> rel x y = False -> rel x y = rel y x
lemma_f rel is_reflexive_rel rel_true_implies_equality_rel x y rel_x_y_is_false = 
  let x_is_not_y = reflexive_rel_false_implies_not_equal {x} {y} rel is_reflexive_rel rel_x_y_is_false in
  let y_is_not_x = negEqSym x_is_not_y in
  let rel_y_x_is_false = rel_true_implies_equality_contrapositive rel rel_true_implies_equality_rel y_is_not_x in
    trans rel_x_y_is_false $ sym rel_y_x_is_false
  
-- If we prove prop in the case rel x y = False and rel x y = True, then we have proved prop in all cases.
elim_t_or_f_rel: {prop: Type} -> (rel : t -> t -> Bool) -> (x : t) -> (y : t) -> (rel x y = False -> prop, rel x y = True -> prop) -> prop
elim_t_or_f_rel {prop} rel x y t_or_f_implies_prop with (has_value_dpair rel x y)
  | (False ** rel_x_y_is_value) = fst t_or_f_implies_prop $ rel_x_y_is_value
  | (True ** rel_x_y_is_value) = snd t_or_f_implies_prop $ rel_x_y_is_value

-- If a relationship is reflexive, and implies intensional equality, then it is symmetric
symmetric_eq_from_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> rel_true_implies_equality rel -> is_symmetric rel
symmetric_eq_from_equal {t} rel is_reflexive_rel rel_true_implies_equality_rel x y =
  let t_hyp = lemma_t rel is_reflexive_rel rel_true_implies_equality_rel x y in
  let f_hyp = lemma_f rel is_reflexive_rel rel_true_implies_equality_rel x y in
    elim_t_or_f_rel {prop=(rel x y = rel y x)} rel x y (f_hyp, t_hyp)
    
-- If a relationship is reflexive, and implies intensional equality, then it is transitive
transitive_eq_from_equal : (rel : t -> t -> Bool) -> is_reflexive rel -> rel_true_implies_equality rel -> is_transitive rel
transitive_eq_from_equal {t} rel is_reflexive_rel rel_true_implies_equality_rel x y z rel_x_y_is_true = 
  let x_is_y = rel_true_implies_equality_rel x y rel_x_y_is_true in 
  rewrite x_is_y in Refl

-- an example involving Eq Bool

bool_is_reflexive : (x : Bool) -> x == x = True
bool_is_reflexive False = Refl
bool_is_reflexive True = Refl

bool_eq_rel_true_implies_equality : rel_true_implies_equality {t=Bool} (==)
bool_eq_rel_true_implies_equality False False prf = Refl
bool_eq_rel_true_implies_equality False True prf = prf
bool_eq_rel_true_implies_equality True False prf = sym prf
bool_eq_rel_true_implies_equality True True prf = Refl

bool_eq_rel_false_implies_inequality : rel_false_implies_inequality {t=Bool} (==)
bool_eq_rel_false_implies_inequality False False prf prf2 = trueNotFalse prf
bool_eq_rel_false_implies_inequality False True prf prf2 = trueNotFalse $ sym prf2
bool_eq_rel_false_implies_inequality True False prf prf2 = trueNotFalse prf2
bool_eq_rel_false_implies_inequality True True prf prf2 = trueNotFalse prf

bool_eq_is_symmetric : (x : Bool) -> (y : Bool) -> x == y = y == x
bool_eq_is_symmetric = symmetric_eq_from_equal (==) bool_is_reflexive bool_eq_rel_true_implies_equality

bool_eq_is_transitive : (x : Bool) -> (y : Bool) -> (z : Bool) -> x == y = True -> x == z = y == z
bool_eq_is_transitive = transitive_eq_from_equal (==) bool_is_reflexive bool_eq_rel_true_implies_equality
