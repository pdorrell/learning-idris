module EqualityExamples

%default total

data ABC = A | B | C

equals_abc : ABC -> ABC -> Bool
equals_abc A B = True
equals_abc B C = True
equals_abc C A = True
equals_abc _ _ = False

Eq ABC where
  (==) = equals_abc

abc_not_reflexive : A == B = not (B == A)
abc_not_reflexive = Refl
