import NatLemmas

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
  
Nat_ : Type
Nat_ = IntensionalSetoid Nat

Nat_3 : Nat_
Nat_3 = 3

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_
  
Setoid Integer_ where
  eq (MkInteger x1 x2) (MkInteger y1 y2) = x1 + y2 = x2 + y1
  
  refl_eq {x=MkInteger x1 x2} = nat_lemmas.plus_comm x1 x2
  
  symm_eq {x=MkInteger x1 x2} {y=MkInteger y1 y2} x_eq_y = 
      let e1 = the (y2 + x1 = x1 + y2) $ nat_lemmas.plus_comm y2 x1
          e2 = the (x2 + y1 = y1 + x2) $ nat_lemmas.plus_comm x2 y1
          e3 = the (x1 + y2 = x2 + y1) $ x_eq_y
       in sym $ trans e1 $ trans e3 e2
       
  trans_eq {x=MkInteger x1 x2} {y=MkInteger y1 y2} {z=MkInteger z1 z2} x_eq_y y_eq_z = 
      let e1 = the (x1 + y2 = x2 + y1) $ x_eq_y
          e2 = the (y1 + z2 = y2 + z1) $ y_eq_z
          e3 = the ((x1 + y2) + (y1 + z2) = (x2 + y1) + (y1 + z2)) $ cong {f = \n => n + (y1 + z2)} e1
          e4 = the ((x1 + y2) + (y1 + z2) = (x2 + y1) + (y2 + z1)) $ rewrite sym e2 in e3
          e5 = the ((x1 + y2) + (y1 + z2) = (x1 + z2) + (y2 + y1)) $ nat_lemmas.abcd_to_adbc_lemma x1 y2 y1 z2
          e6 = the ((x2 + y1) + (y2 + z1) = (x2 + z1) + (y1 + y2)) $ nat_lemmas.abcd_to_adbc_lemma x2 y1 y2 z1
          e7 = the ((x1 + z2) + (y2 + y1) = (x2 + z1) + (y1 + y2)) $ trans (sym e5) $ trans e4 e6
          e8 = the ((x2 + z1) + (y1 + y2) = (x2 + z1) + (y2 + y1)) $ cong $ nat_lemmas.plus_comm y1 y2
          e9 = the ((x1 + z2) + (y2 + y1) = (x2 + z1) + (y2 + y1)) $ trans e7 e8
      in the ((x1 + z2) = (x2 + z1)) $ nat_lemmas.plus_right_cancel (x1 + z2) (x2 + z1) (y2 + y1) $ e9

Num Integer_ where
  (MkInteger x1 x2) + (MkInteger y1 y2) = MkInteger (x1 + y1) (x2 + y2)
  (MkInteger x1 x2) * (MkInteger y1 y2) = MkInteger (x1 * y1 + x2 * y2) (x1 * y2 + x2 * y1)
  fromInteger x = if x < 0 
                     then MkInteger 0 (fromInteger (- x))
                     else MkInteger (fromInteger x) 0
