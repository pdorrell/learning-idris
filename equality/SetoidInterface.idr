%default total

interface Setoid t where
  eq : t -> t -> Type
  refl_eq : {x : t} -> eq x x
  symm_eq : {x : t} -> {y : t} -> eq x y -> eq y x
  trans_eq : {x : t} -> {y : t} -> {z : t} -> eq x y -> eq y z -> eq x z
  
interface Wraps (from : Type) (to : Type) | to where
  wrap   : from -> to
  unwrap : to   -> from
  
data IntensionalSetoid : (t : Type) -> Type where
  Wrap : t -> IntensionalSetoid t

Setoid (IntensionalSetoid t) where
  eq (Wrap x) (Wrap y) = x = y
  refl_eq {x=Wrap x} = Refl
  symm_eq {x=Wrap x} {y=Wrap y} = sym
  trans_eq {x=Wrap x} {y=Wrap y} {z=Wrap z} = trans
  
Wraps t (IntensionalSetoid t) where
  wrap x = Wrap x
  unwrap (Wrap x) = x

Num t => Num (IntensionalSetoid t) where
  x + y = wrap (unwrap x + unwrap y)
  x * y = wrap (unwrap x * unwrap y)
  fromInteger x = wrap (fromInteger x)
