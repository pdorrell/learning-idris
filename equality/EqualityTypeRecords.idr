import NatLemmas

%default total

record HasEquality t where
  constructor MkHasEquality
  eq : t -> t -> Type
  refl_eq : (x : t) -> eq x x
  symm_eq : (x : t) -> (y : t) -> eq x y -> eq y x
  trans_eq : (x : t) -> (y : t) -> (z : t) -> eq x y -> eq y z -> eq x z
  
NatEquality : HasEquality Nat
NatEquality = MkHasEquality nat_eq nat_refl_eq nat_symm_eq nat_trans_eq where
    nat_eq : Nat -> Nat -> Type
    nat_eq x y = x = y
    nat_refl_eq : (x : Nat) -> nat_eq x x
    nat_refl_eq x = Refl
    nat_symm_eq : (x : Nat) -> (y : Nat) -> nat_eq x y -> nat_eq y x
    nat_symm_eq x y x_eq_y = sym $ the (x = y) x_eq_y
    nat_trans_eq : (x : Nat) -> (y : Nat) -> (z : Nat) -> nat_eq x y -> nat_eq y z -> nat_eq x z
    nat_trans_eq x y z x_eq_y y_eq_z = trans x_eq_y y_eq_z

data EqualPair : (t : Type) -> (eq_type: HasEquality t) -> Type where
  MkEqualPair : (x : t) -> (y : t) -> eq eq_type x y -> EqualPair t eq_type
  
Nat' : Type
Nat' = EqualPair Nat NatEquality

nat'3 : Nat'
nat'3 = MkEqualPair 3 3 Refl
  
double_it : Nat' -> Nat'
double_it (MkEqualPair x y x_is_y) = MkEqualPair (x + x) (y + y) (cong {f=\x => x + x} x_is_y)

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_

bcd_lemma : (b : Nat) -> (c : Nat) -> (d : Nat) -> 
                b + (c + d) = d + (b + c)
bcd_lemma b c d = 
  let e1 = the (b + (c + d) = (b + c) + d) $ sym $ nat_lemmas.plus_assoc b c d
      e2 = the ((b + c) + d = d + (b + c)) $ nat_lemmas.plus_comm (b + c) d
  in the (b + (c + d) = d + (b + c)) $ trans e1 e2
      
abcd_lemma : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> 
                (a + b) + (c + d) = (a + d) + (b + c)
abcd_lemma a b c d = 
  let e1 = the ((a + b) + (c + d) = a + (b + (c + d))) $ nat_lemmas.plus_assoc a b (c + d)
      e2 = the ((a + d) + (b + c) = a + (d + (b + c))) $ nat_lemmas.plus_assoc a d (b + c)
      e3 = the (a + (b + (c + d)) = a + (d + (b + c))) $ cong $ bcd_lemma b c d
    in the ((a + b) + (c + d) = (a + d) + (b + c)) $ trans e1 (trans e3 (sym e2))

IntegerEquality : HasEquality Integer_
IntegerEquality = MkHasEquality int_eq int_refl_eq int_symm_eq int_trans_eq where
    int_eq : Integer_ -> Integer_ -> Type
    int_eq (MkInteger x1 x2) (MkInteger y1 y2) = x1 + y2 = x2 + y1
    int_refl_eq : (x : Integer_) -> int_eq x x
    int_refl_eq (MkInteger x1 x2) = nat_lemmas.plus_comm x1 x2
    int_symm_eq : (x : Integer_) -> (y : Integer_) -> int_eq x y -> int_eq y x
    int_symm_eq (MkInteger x1 x2) (MkInteger y1 y2) x_eq_y = 
      let e1 = the (y2 + x1 = x1 + y2) $ nat_lemmas.plus_comm y2 x1
          e2 = the (x2 + y1 = y1 + x2) $ nat_lemmas.plus_comm x2 y1
          e3 = the (x1 + y2 = x2 + y1) $ x_eq_y
       in sym $ trans e1 $ trans e3 e2
        
    int_trans_eq : (x : Integer_) -> (y : Integer_) -> (z : Integer_) -> 
                      int_eq x y -> int_eq y z -> int_eq x z
    int_trans_eq (MkInteger x1 x2) (MkInteger y1 y2) (MkInteger z1 z2) x_eq_y y_eq_z = 
      let e1 = the (x1 + y2 = x2 + y1) $ x_eq_y
          e2 = the (y1 + z2 = y2 + z1) $ y_eq_z
          e3 = the ((x1 + y2) + (y1 + z2) = (x2 + y1) + (y1 + z2)) $ cong {f = \n => n + (y1 + z2)} e1
          e4 = the ((x1 + y2) + (y1 + z2) = (x2 + y1) + (y2 + z1)) $ rewrite sym e2 in e3
          e5 = the ((x1 + y2) + (y1 + z2) = (x1 + z2) + (y2 + y1)) $ abcd_lemma x1 y2 y1 z2
          e6 = the ((x2 + y1) + (y2 + z1) = (x2 + z1) + (y1 + y2)) $ abcd_lemma x2 y1 y2 z1
          e7 = the ((x1 + z2) + (y2 + y1) = (x2 + z1) + (y1 + y2)) $ trans (sym e5) $ trans e4 e6
          e8 = the ((x2 + z1) + (y1 + y2) = (x2 + z1) + (y2 + y1)) $ cong $ nat_lemmas.plus_comm y1 y2
          e9 = the ((x1 + z2) + (y2 + y1) = (x2 + z1) + (y2 + y1)) $ trans e7 e8
      in the ((x1 + z2) = (x2 + z1)) $ nat_lemmas.plus_right_cancel (x1 + z2) (x2 + z1) (y2 + y1) $ e9
    
Integer' : Type
Integer' = EqualPair Integer_ IntegerEquality

