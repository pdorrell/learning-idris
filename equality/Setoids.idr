import NatLemmas

%default total

record Setoid where
  constructor MkSetoid
  carrier : Type
  eq : carrier -> carrier -> Type
  refl_eq : (x : carrier) -> eq x x
  symm_eq : (x : carrier) -> (y : carrier) -> eq x y -> eq y x
  trans_eq : (x : carrier) -> (y : carrier) -> (z : carrier) -> eq x y -> eq y z -> eq x z
  
IntensionalSetoid : (t : Type) -> Setoid
IntensionalSetoid t = MkSetoid t t_eq t_refl_eq t_symm_eq t_trans_eq where
    t_eq : t -> t -> Type
    t_eq x y = x = y

    t_refl_eq : (x : t) -> t_eq x x
    t_refl_eq x = Refl
    
    t_symm_eq : (x : t) -> (y : t) -> t_eq x y -> t_eq y x
    t_symm_eq x y x_eq_y = sym $ the (x = y) x_eq_y
    
    t_trans_eq : (x : t) -> (y : t) -> (z : t) -> t_eq x y -> t_eq y z -> t_eq x z
    t_trans_eq x y z x_eq_y y_eq_z = trans x_eq_y y_eq_z

    
data EqualPair : (eq_type: Setoid) -> Type where
  MkEqualPair : (x : carrier eq_type) -> (y : carrier eq_type) -> eq eq_type x y -> EqualPair eq_type
  
identical_pair : {eq_type: Setoid} -> (x : carrier eq_type) -> EqualPair eq_type
identical_pair {eq_type} x = MkEqualPair x x (refl_eq eq_type x)

eq_respects_binary_op: (eq_type : Setoid) -> (op: (carrier eq_type) -> (carrier eq_type) -> (carrier eq_type)) -> Type
eq_respects_binary_op eq_type op = 
  let t = carrier eq_type
  in (x1 : t) -> (x2 : t) -> (y1 : t) -> (y2 : t) -> 
        (eq eq_type x1 x2) -> (eq eq_type y1 y2) -> (eq eq_type (op x1 y1) (op x2 y2))

eq_respects_unary_op: (eq_type : Setoid) -> (op: carrier eq_type -> carrier eq_type) -> Type
eq_respects_unary_op eq_type op =
  let t = carrier eq_type
  in (x1 : t) -> (x2 : t) -> (eq eq_type x1 x2) -> (eq eq_type (op x1) (op x2))

NatSetoid : Setoid
NatSetoid = IntensionalSetoid Nat
  
data Nat' : Type where
  MkNat' : EqualPair NatSetoid -> Nat'
  
interface WrappedEqualPair (t : Type) where
  setoid : Setoid
  wrap : EqualPair setoid -> t
  unwrap : t -> EqualPair setoid
  
WrappedEqualPair Nat' where
  setoid = NatSetoid
  wrap pair = MkNat' pair
  unwrap (MkNat' pair) = pair
  
EqualIntensionalPair : (t : Type) -> Type
EqualIntensionalPair t = EqualPair (IntensionalSetoid t)

BinaryOp : (t : Type) -> Type
BinaryOp t = t -> t -> t

lift_binary_op_to_intensional_equal_pair : (op : BinaryOp t) -> BinaryOp (EqualPair (IntensionalSetoid t))
lift_binary_op_to_intensional_equal_pair {t} op (MkEqualPair x1 x2 x1_is_x2) (MkEqualPair y1 y2 y1_is_y2)  =
    let e1 = the (x1 = x2) x1_is_x2
        e2 = the (y1 = y2) y1_is_y2
        e3 = the (op x1 y1 = op x1 y1) Refl
    in MkEqualPair (op x1 y1) (op x2 y2) (the (op x1 y1 = op x2 y2) (rewrite e1 in rewrite e2 in Refl))
    
--fun : (WrappedEqualPair wept) => BinaryOp (EqualPair Main.setoid) -> BinaryOp wept
    
Num Nat' where
  x + y = 
    let unwrapped_x = unwrap x
        unwrapped_y = unwrap y
    in wrap ((lift_binary_op_to_intensional_equal_pair (+)) unwrapped_x unwrapped_y)
--  (MkNat' x) + (MkNat' y) = MkNat' ((lift_binary_op_to_intensional_equal_pair (+)) x y)
  (MkNat' x) * (MkNat' y) = MkNat' ((lift_binary_op_to_intensional_equal_pair (*)) x y)
  fromInteger x = MkNat' (identical_pair (fromInteger x))
  
nat'3 : Nat'
nat'3 = 3



double_nat : Nat -> Nat
double_nat x = x + x

lift_fun_to_intensional_eq : {eq_type_t2 : Setoid} -> (f : t1 -> carrier eq_type_t2) -> 
                         (EqualPair (IntensionalSetoid t1) -> EqualPair eq_type_t2)
lift_fun_to_intensional_eq {eq_type_t2} f (MkEqualPair x y eq_x_y) = 
  MkEqualPair (f x) (f y) eq_fx_fy where
     eq_fx_fy : eq eq_type_t2 (f x) (f y)
     eq_fx_fy = 
       let x_is_y = the (x = y) eq_x_y
           fx_is_fy = cong {f=f} x_is_y
           eq_fy_fy = refl_eq eq_type_t2 (f y)
         in rewrite fx_is_fy in the (eq eq_type_t2 (f y) (f y)) eq_fy_fy

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_
  
Num Integer_ where
  (MkInteger x1 x2) + (MkInteger y1 y2) = MkInteger (x1 + y1) (x2 + y2)
  (MkInteger x1 x2) * (MkInteger y1 y2) = MkInteger (x1 * y1 + x2 * y2) (x1 * y2 + x2 * y1)
  fromInteger x = if x < 0 
                     then MkInteger 0 (fromInteger (- x))
                     else MkInteger (fromInteger x) 0

Neg Integer_ where
  negate (MkInteger x1 x2) = MkInteger x2 x1
  (MkInteger x1 x2) - (MkInteger y1 y2) = MkInteger (x1 + y2) (x2 + y1)
  abs (MkInteger x1 x2) = if x1 > x2
                            then MkInteger x1 x2
                            else MkInteger x2 x1
  
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

IntegerSetoid : Setoid
IntegerSetoid = MkSetoid Integer_ int_eq int_refl_eq int_symm_eq int_trans_eq where
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
    
data Integer' : Type where
  MkInteger' : EqualPair IntegerSetoid -> Integer'

Integer'3 : Integer'
Integer'3 = ?hole