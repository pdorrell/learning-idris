%default total

disjointTy : Nat -> Type
disjointTy Z = ()
disjointTy (S k) = Void
    
one_is_not_equal_to_zero : (S Z = Z) -> Void
one_is_not_equal_to_zero Refl impossible

ident : a -> a
ident x = x

not_only_ident_has_ident_type: ({a: Type} -> (f : a -> a) -> (x : a) -> f x = x) -> Void
not_only_ident_has_ident_type hyp = one_is_not_equal_to_zero (hyp S Z)

only_ident_has_ident_type: (f : a -> a) -> (x : a) -> f x = x
only_ident_has_ident_type f x = ?only_ident_has_ident_type_rhs
