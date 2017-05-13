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
  equals_is_reflexive : (x : t) -> x == x = True
  equals_is_symmetric : (x : t) -> (y : t) -> x == y = y == x
  equals_is_transitive : (x : t) -> (y : t) -> (z : t) -> x == y = True -> x == z = y == z
  
bool_equality_is_reflexive : (x : Bool) -> x == x = True
bool_equality_is_reflexive False = Refl
bool_equality_is_reflexive True = Refl

bool_equality_is_symmetric : (x : Bool) -> (y : Bool) -> x == y = y == x
bool_equality_is_symmetric False False = Refl
bool_equality_is_symmetric False True = Refl
bool_equality_is_symmetric True False = Refl
bool_equality_is_symmetric True True = Refl

bool_equality_is_transitive : (x : Bool) -> (y : Bool) -> (z : Bool) -> x == y = True -> x == z = y == z
bool_equality_is_transitive False False z Refl = Refl
bool_equality_is_transitive False True _ Refl impossible
bool_equality_is_transitive True False _ Refl impossible
bool_equality_is_transitive True True z Refl = Refl
  
LawfulEq Bool where
  equals_is_reflexive = bool_equality_is_reflexive
  equals_is_symmetric = bool_equality_is_symmetric
  equals_is_transitive = bool_equality_is_transitive
  
is_a_or_b : ABC -> Bool
is_a_or_b A = True
is_a_or_b B = True
is_a_or_b C = False

  
a_equals_b : ABC -> ABC -> Bool
a_equals_b x y = is_a_or_b x == is_a_or_b y

Eq ABC where
  (==) = a_equals_b

a_equals_b_is_reflexive : (x : ABC) -> x == x = True
a_equals_b_is_reflexive x = bool_equality_is_reflexive (is_a_or_b x)

a_equals_b_is_symmetric : (x : ABC) -> (y : ABC) -> x == y = y == x
a_equals_b_is_symmetric x y = bool_equality_is_symmetric (is_a_or_b x) (is_a_or_b y)

a_equals_b_is_transitive : (x : ABC) -> (y : ABC) -> (z : ABC) -> x == y = True -> x == z = y == z
a_equals_b_is_transitive x y z = bool_equality_is_transitive (is_a_or_b x) (is_a_or_b y) (is_a_or_b z)

LawfulEq ABC where
  equals_is_reflexive = a_equals_b_is_reflexive
  equals_is_symmetric = a_equals_b_is_symmetric
  equals_is_transitive = a_equals_b_is_transitive



