import NatLemmas

%default total

infixl 5 =.

interface HasEquality  t where
  (=.) : t -> t -> Type
  refl_eq : (x : t) -> x =. x
  
HasEquality Nat where
  x =. y = x = y
  refl_eq x = Refl
  
refl_lemma : HasEquality t => (x : t) -> (y : t) -> x = y -> x =.y
refl_lemma x x Refl = refl_eq x

HasIntentionalEquality : (t : Type) -> Type
HasIntentionalEquality t = HasEquality t -> (x : t) -> (y : t) -> x =.y -> x = y

data Equated : (t : Type) -> Type where
  MkEquated : HasEquality t => (x : t) -> (y : t) -> x =. y -> Equated t

Nat' : Type
Nat' = Equated Nat

double_it : Nat' -> Nat'
double_it (MkEquated x y x_is_y) = MkEquated (x + x) (y + y) (cong {f=\x => x + x} x_is_y)

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_
  
HasEquality Integer_ where
  (MkInteger x1 x2) =. (MkInteger y1 y2) = x1 + y2 = x2 + y1
  refl_eq (MkInteger x1 x2) = nat_lemmas.plus_commutative x1 x2
  
Integer' : Type
Integer' = Equated Integer_
  
lift_fun_to_equated_type : (HasEquality t2) => HasIntentionalEquality t1 -> (f : t1 -> t2) -> (Equated t1 -> Equated t2)
lift_fun_to_equated_type t1_has_intensional_equality f (MkEquated x y x_is_y) = 
  let x_equals_y = t1_has_intensional_equality %implementation x y x_is_y in
  let fx_equals_fy = cong {f=f} x_equals_y in
  let fx_is_fy = refl_lemma (f x) (f y) fx_equals_fy in 
    MkEquated (f x) (f y) fx_is_fy
