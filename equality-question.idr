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
  
bool_lemma : (x : Bool) -> x == x = True
bool_lemma False = Refl
bool_lemma True = Refl

lemma2 :  (x : ABC) -> (is_a_or_b x) == (is_a_or_b x) = True
lemma2 x = bool_lemma (is_a_or_b x)

a_equals_b_is_reflexive : (x : ABC) -> (x == x) = True
a_equals_b_is_reflexive x = lemma2 x

a_equals_b_is_symmetric : (x : ABC) -> (y : ABC) -> x == y = y == x
a_equals_b_is_symmetric A A = Refl
a_equals_b_is_symmetric A B = Refl
a_equals_b_is_symmetric A C = Refl
a_equals_b_is_symmetric B A = Refl
a_equals_b_is_symmetric B B = Refl
a_equals_b_is_symmetric B C = Refl
a_equals_b_is_symmetric C A = Refl
a_equals_b_is_symmetric C B = Refl
a_equals_b_is_symmetric C C = Refl
