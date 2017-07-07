%default total

interface Group t where
  Unit: t
  (*): t -> t -> t
  Inv: t -> t

  assoc: (a : t) -> (b : t) -> (c : t) -> ((a*b)*c = a*(b*c))
  neutralL: (x: t) -> (a : t) -> a * Unit = a
  neutralR: (x: t) -> (a : t) -> Unit * a = a
  invUnitL: (x: t) -> (a : t) -> a * (Inv a) = Unit
  invUnitR: (x: t) -> (a : t) -> (Inv a) * a = Unit

cong : Group t => (a : t) -> (b : t) -> (c: t) -> a = b -> a*c = b*c
cong a b c post = rewrite post in Refl

neutralL1: Group t => (x: t) -> (a : t) -> a = a * Unit
neutralL1 x a = rewrite neutralL x a in Refl

neutralR1: Group t => (x: t) -> (a : t) -> a = Unit * a
neutralR1 x a = rewrite neutralR x a in Refl

is_left_unit : Group t => (x : t) -> Type
is_left_unit x = (y : t) -> x * y = y

only_one_left_unit : Group t => (x : t) -> is_left_unit x -> x = Unit
only_one_left_unit x is_left_unit_x = 
  let x_times_unit_is_unit = is_left_unit_x Unit in
  let x_times_unit_is_x = neutralL Unit x in
    trans (sym x_times_unit_is_x) x_times_unit_is_unit

is_right_unit : Group t => (x : t) -> Type
is_right_unit x = (y : t) -> y * x = y

only_one_right_unit : Group t => (x : t) -> is_right_unit x -> x = Unit
only_one_right_unit x is_right_unit_x = 
  let unit_times_x_is_unit = is_right_unit_x Unit in
  let unit_times_x_is_x = neutralR Unit x in
    trans (sym unit_times_x_is_x) unit_times_x_is_unit
