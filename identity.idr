%default total

-- An attempt to express the idea that the only function of type a->a is the identity function
only_ident_has_ident_type: (f : a -> a) -> (x : a) -> f x = x
only_ident_has_ident_type f x = ?only_ident_has_ident_type_rhs

-- But this is wrong because 'a' is an implicit argument which can be chosen _before_ f

-- Eg the following generates the same hole as only_ident_has_ident_type
only_ident_has_ident_type2: {a: Type} -> (f : a -> a) -> (x : a) -> f x = x
only_ident_has_ident_type2 f x = ?only_ident_has_ident_type2_rhs

-- And here is a proof that only_ident_has_ident_type2 is _not_ true
-- (Note: in this proof the declaration of {a: Type} is required - for some reason)
-- It uses the function S which is of type Nat->Nat as a counter-example.
not_only_ident_has_ident_type: ({a: Type} -> (f : a -> a) -> (x : a) -> f x = x) -> Void
not_only_ident_has_ident_type hyp = one_is_not_equal_to_zero (hyp S Z) where
  one_is_not_equal_to_zero : (S Z = Z) -> Void
  one_is_not_equal_to_zero Refl impossible
