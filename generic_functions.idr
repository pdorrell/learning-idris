%default total

GenericEndomorphism: Type
GenericEndomorphism = (t: Type) -> (t -> t)

id_is_an_example : GenericEndomorphism
id_is_an_example t = id

id_is_the_only_example : (f : GenericEndomorphism) -> (t : Type) -> (x : t) -> f t x = x
id_is_the_only_example f t x = ?id_is_the_only_example_rhs

