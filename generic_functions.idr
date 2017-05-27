%default total

GenericEndomorphism: Type
GenericEndomorphism = (t: Type) -> (t -> t)

id_is_generic : GenericEndomorphism
id_is_generic t = id

id_is_only_generic : (f : GenericEndomorphism) -> (t : Type) -> (x : t) -> f t x = x
id_is_only_generic f t x = ?id_is_only_generic_rhs
