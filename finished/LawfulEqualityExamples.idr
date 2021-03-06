module LawfulEqualityExamples

import LawfulEquality

%default total

data ABC = A | B | C

is_a_or_b : ABC -> Bool
is_a_or_b A = True
is_a_or_b B = True
is_a_or_b C = False
  
Eq ABC where
  (==) = \x, y => is_a_or_b x == is_a_or_b y
  
LawfulEq ABC where
  eq_is_reflexive = \x => eq_is_reflexive (is_a_or_b x)
  eq_is_symmetric = \x, y => eq_is_symmetric (is_a_or_b x) (is_a_or_b y)
  eq_is_transitive = \x, y, z => eq_is_transitive (is_a_or_b x) (is_a_or_b y) (is_a_or_b z)

-- And now for some bad unlawful equality ...

bad_equals_abc : ABC -> ABC -> Bool
bad_equals_abc A B = True
bad_equals_abc B C = True
bad_equals_abc C A = True
bad_equals_abc _ _ = False

[BadEquality] Eq ABC where
  (==) = bad_equals_abc

bad_equals_abc_not_symmetric : bad_equals_abc A B = not $ bad_equals_abc B A
bad_equals_abc_not_symmetric = Refl

