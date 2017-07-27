import NatLemmas

%default total

record HasEqualityRec t where
  constructor MkHasEquality
  eq : t -> t -> Type
  refl_eq : (x : t) -> eq x x
  symm_eq : (x : t) -> (y : t) -> eq x y -> eq y x
  
NatEquality : HasEqualityRec Nat
NatEquality = MkHasEquality nat_eq nat_refl_eq nat_symm_eq where
    nat_eq : Nat -> Nat -> Type
    nat_eq x y = x = y
    nat_refl_eq : (x : Nat) -> nat_eq x x
    nat_refl_eq x = Refl
    nat_symm_eq : (x : Nat) -> (y : Nat) -> nat_eq x y -> nat_eq y x
    nat_symm_eq x y x_eq_y = sym $ the (x = y) x_eq_y

data EqualPair : (t : Type) -> (eq_type: HasEqualityRec t) -> Type where
  MkEqualPair : (x : t) -> (y : t) -> eq eq_type x y -> EqualPair t eq_type
  
Nat'' : Type
Nat'' = EqualPair Nat NatEquality

nat''3 : Nat''
nat''3 = MkEqualPair 3 3 Refl
  
double_it_rec : Nat'' -> Nat''
double_it_rec (MkEqualPair x y x_is_y) = MkEqualPair (x + x) (y + y) (cong {f=\x => x + x} x_is_y)

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_
  
IntegerEquality : HasEqualityRec Integer_
IntegerEquality = MkHasEquality int_eq int_refl_eq int_symm_eq where
    int_eq : Integer_ -> Integer_ -> Type
    int_eq (MkInteger x1 x2) (MkInteger y1 y2) = x1 + y2 = x2 + y1
    int_refl_eq : (x : Integer_) -> int_eq x x
    int_refl_eq (MkInteger x1 x2) = nat_lemmas.plus_commutative x1 x2
    int_symm_eq : (x : Integer_) -> (y : Integer_) -> int_eq x y -> int_eq y x
    int_symm_eq (MkInteger x1 x2) (MkInteger y1 y2) x_is_y = ?int_symm_eq_rhs_2
    
Integer'' : Type
Integer'' = EqualPair Integer_ IntegerEquality

