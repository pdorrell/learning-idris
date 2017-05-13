module EqualityExamples

%default total

data ABC = A | B | C

bad_equals_abc : ABC -> ABC -> Bool
bad_equals_abc A B = True
bad_equals_abc B C = True
bad_equals_abc C A = True
bad_equals_abc _ _ = False

--[BadEquality] Eq ABC where
--  (==) = bad_equals_abc

bad_equals_abc_not_reflexive : bad_equals_abc A B = not $ bad_equals_abc B A
bad_equals_abc_not_reflexive = Refl

interface Eq t => LawfulEq t where
  eq_is_reflexive : (x : t) -> x == x = True
  eq_is_symmetric : (x : t) -> (y : t) -> x == y = y == x
  eq_is_transitive : (x : t) -> (y : t) -> (z : t) -> x == y = True -> x == z = y == z
  
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
  
LawfulEq Bool where
  eq_is_reflexive = bool_equality_lemmas.reflexive
  eq_is_symmetric = bool_equality_lemmas.symmetric
  eq_is_transitive = bool_equality_lemmas.transitive
  
is_a_or_b : ABC -> Bool
is_a_or_b A = True
is_a_or_b B = True
is_a_or_b C = False

  
a_equals_b : ABC -> ABC -> Bool
a_equals_b x y = is_a_or_b x == is_a_or_b y

Eq ABC where
  (==) = a_equals_b

a_equals_b_is_reflexive : (x : ABC) -> x == x = True
a_equals_b_is_reflexive x = eq_is_reflexive (is_a_or_b x)

a_equals_b_is_symmetric : (x : ABC) -> (y : ABC) -> x == y = y == x
a_equals_b_is_symmetric x y = eq_is_symmetric (is_a_or_b x) (is_a_or_b y)

a_equals_b_is_transitive : (x : ABC) -> (y : ABC) -> (z : ABC) -> x == y = True -> x == z = y == z
a_equals_b_is_transitive x y z = eq_is_transitive (is_a_or_b x) (is_a_or_b y) (is_a_or_b z)

LawfulEq ABC where
  eq_is_reflexive = a_equals_b_is_reflexive
  eq_is_symmetric = a_equals_b_is_symmetric
  eq_is_transitive = a_equals_b_is_transitive



