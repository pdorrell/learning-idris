module EqualityExamples

%default total

data ABC = A | B | C

is_a_or_b : ABC -> Bool
is_a_or_b A = True
is_a_or_b B = True
is_a_or_b C = False

a_equals_b : ABC -> ABC -> Bool
a_equals_b x y = is_a_or_b x == is_a_or_b y

Eq ABC where
  (==) = a_equals_b
  
bool_equality_is_reflexive : (x : Bool) -> x == x = True
bool_equality_is_reflexive False = Refl
bool_equality_is_reflexive True = Refl

a_equals_b_is_reflexive : (x : ABC) -> (x == x) = True
a_equals_b_is_reflexive x = bool_equality_is_reflexive (is_a_or_b x)

bool_equality_is_symmetric : (x : Bool) -> (y : Bool) -> x == y = y == x
bool_equality_is_symmetric False False = Refl
bool_equality_is_symmetric False True = Refl
bool_equality_is_symmetric True False = Refl
bool_equality_is_symmetric True True = Refl

a_equals_b_is_symmetric : (x : ABC) -> (y : ABC) -> x == y = y == x
a_equals_b_is_symmetric x y = bool_equality_is_symmetric (is_a_or_b x) (is_a_or_b y)

bool_equality_is_transitive : (x : Bool) -> (y : Bool) -> (z : Bool) -> x == y = True -> x == z = y == z
bool_equality_is_transitive False False z Refl = Refl
bool_equality_is_transitive False True _ Refl impossible
bool_equality_is_transitive True False _ Refl impossible
bool_equality_is_transitive True True z Refl = Refl
