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
  
is_a_or_b : ABC -> Bool
is_a_or_b A = True
is_a_or_b B = True
is_a_or_b C = False

  
a_equals_b : ABC -> ABC -> Bool
a_equals_b x y = is_a_or_b x == is_a_or_b y

Eq ABC where
  (==) = a_equals_b

a_equals_b_is_reflexive : (x : ABC) -> x == x = True
a_equals_b_is_reflexive A = Refl
a_equals_b_is_reflexive B = Refl
a_equals_b_is_reflexive C = Refl

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

LawfulEq ABC where
  equals_is_reflexive = a_equals_b_is_reflexive
  equals_is_symmetric = a_equals_b_is_symmetric
  equals_is_transitive = ?a_equals_b_is_transitive



