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

