%default total

infixl 5 =.

interface HasEquality  t where
  (=.) : t -> t -> Type
  symm_eq : (x : t) -> x =. x
  
HasEquality Nat where
  x =. y = x = y
  symm_eq x = Refl
  
symm_lemma : HasEquality t => (x : t) -> (y : t) -> x = y -> x =.y
symm_lemma x x Refl = symm_eq x

HasIntentionalEquality : (t : Type) -> Type
HasIntentionalEquality t = HasEquality t -> (x : t) -> (y : t) -> x =.y -> x = y

data Equated : (t : Type) -> Type where
  EqualPair : HasEquality t => (x : t) -> (y : t) -> x =. y -> Equated t

Nat' : Type
Nat' = Equated Nat

double_it : Nat' -> Nat'
double_it (EqualPair x y x_is_y) = EqualPair (x + x) (y + y) (cong {f=\x => x + x} x_is_y)

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_
  
namespace nat_lemmas

  zero_right_ident : (x : Nat) -> x = x + 0
  zero_right_ident Z = Refl
  zero_right_ident (S k) = rewrite zero_right_ident k in Refl
  
  s_on_right_addend : (x : Nat) -> (y : Nat) -> S (x + y) = x + S y
  s_on_right_addend Z y = Refl
  s_on_right_addend (S k) y = rewrite s_on_right_addend k y in Refl

  plus_commutative : (x : Nat) -> (y : Nat) -> x + y = y + x
  plus_commutative Z y = zero_right_ident y
  plus_commutative (S k) y =
    let s_of_y_plus_k_is_y_plus_sk = s_on_right_addend y k in
    let s_of_k_plus_y_is_s_of_y_plus_k = cong {f=S} $ plus_commutative k y in
    trans s_of_k_plus_y_is_s_of_y_plus_k s_of_y_plus_k_is_y_plus_sk

HasEquality Integer_ where
  (MkInteger x1 x2) =. (MkInteger y1 y2) = x1 + y2 = x2 + y1
  symm_eq (MkInteger x1 x2) = nat_lemmas.plus_commutative x1 x2

lift_fun_to_equated_type : (HasEquality t2) => HasIntentionalEquality t1 -> (f : t1 -> t2) -> (Equated t1 -> Equated t2)
lift_fun_to_equated_type t1_has_intensional_equality f (EqualPair x y x_is_y) = 
  let x_equals_y = t1_has_intensional_equality %implementation x y x_is_y in
  let fx_equals_fy = cong {f=f} x_equals_y in
  let fx_is_fy = symm_lemma (f x) (f y) fx_equals_fy in 
    EqualPair (f x) (f y) fx_is_fy
