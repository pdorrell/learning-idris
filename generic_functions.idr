%default total

GenericEndomorphism: Type
GenericEndomorphism = (t: Type) -> (t -> t)

ident_is_generic : GenericEndomorphism
ident_is_generic t = id

ident_is_only_generic : (f : GenericEndomorphism) -> (t : Type) -> (x : t) -> f t x = x
ident_is_only_generic f t x = ?ident_is_only_generic_rhs
