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
  
FunRespectsEq : (Setoid t1, Setoid t2) => (t1 -> t2) -> Type
FunRespectsEq {t1} {t2} f = (x1 : t1) -> (x2 : t1) -> eq x1 x2 -> eq (f x1) (f x2)

data FunctionSetoid : (t1 : Type) -> (t2 : Type) -> Type where
  MkFunction : (Setoid t1, Setoid t2) => (f : t1 -> t2) -> FunRespectsEq f -> FunctionSetoid t1 t2
  
Setoid (FunctionSetoid t1 t2) where
  eq (MkFunction f1 _) (MkFunction f2 _) = (x : t1) -> eq (f1 x) (f2 x)
  refl_eq {x=MkFunction f1 _} x' = refl_eq {x=f1 x'}
  symm_eq {x=MkFunction f1 _} {y=MkFunction f2 _} eq_f1_f2 x' = 
                             symm_eq {x=f1 x'} {y=f2 x'} $ eq_f1_f2 x'
  trans_eq {x=MkFunction f1 _} {y=MkFunction f2 _} {z=MkFunction f3 _} eq_f1_f2 eq_f2_f3 x' = 
                             trans_eq {x=f1 x'} {y=f2 x'} {z=f3 x'} (eq_f1_f2 x') (eq_f2_f3 x')

Num t => Num (IntensionalSetoid t) where
  x + y = wrap (unwrap x + unwrap y)
  x * y = wrap (unwrap x * unwrap y)
  fromInteger x = wrap (fromInteger x)

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_
  
