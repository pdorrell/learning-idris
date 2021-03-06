import NatLemmas

%default total

record Setoid where
  constructor MkSetoid
  carrier : Type
  eq : carrier -> carrier -> Type
  refl_eq : {x : carrier} -> eq x x
  symm_eq : {x : carrier} -> {y : carrier} -> eq x y -> eq y x
  trans_eq : {x : carrier} -> {y : carrier} -> {z : carrier} -> eq x y -> eq y z -> eq x z
  
IntensionalSetoid : (t : Type) -> Setoid
IntensionalSetoid t = MkSetoid t t_eq t_refl_eq t_symm_eq t_trans_eq where
    t_eq : t -> t -> Type
    t_eq x y = x = y

    t_refl_eq : {x : t} -> t_eq x x
    t_refl_eq = Refl
    
    t_symm_eq : {x : t} -> {y : t} -> t_eq x y -> t_eq y x
    t_symm_eq {x} {y} x_eq_y = sym $ the (x = y) x_eq_y
    
    t_trans_eq : {x : t} -> {y : t} -> {z : t} -> t_eq x y -> t_eq y z -> t_eq x z
    t_trans_eq x_eq_y y_eq_z = trans x_eq_y y_eq_z

    
data EqPair : (setoid: Setoid) -> Type where
  MkEqPair : (x : carrier setoid) -> (y : carrier setoid) -> eq setoid x y -> EqPair setoid
  
identical_pair : {setoid: Setoid} -> (x : carrier setoid) -> EqPair setoid
identical_pair {setoid} x = MkEqPair x x (refl_eq setoid)

BinaryOp : (t : Type) -> Type
BinaryOp t = t -> t -> t

CommutativeBy : (op : t -> t -> t2) -> (eq : t2 -> t2 -> Type) -> Type
CommutativeBy {t} op eq = (x : t) -> (y : t) -> eq (op x y) (op y x)

Commutative : (op : t -> t -> t2) -> Type
Commutative op = CommutativeBy op (=)

reflexive : (eq : t -> t -> Type) -> Type
reflexive {t} eq = (x : t) -> eq x x

CommutativeBy_from_Commutative : {op : t -> t -> t2} -> reflexive eq -> Commutative op -> CommutativeBy op eq
CommutativeBy_from_Commutative {t} {op} {eq} refl_eq op_is_comm x y = 
  let e1 = the (op x y = op y x) $ op_is_comm x y
      e2 = the (eq (op x y) (op x y)) $ refl_eq (op x y)
  in rewrite sym e1 in e2
  
bin_op_respects_eq : (op : BinaryOp t) -> (eq : t -> t -> Type) -> Type
bin_op_respects_eq {t} op eq = (x1 : t) -> (x2 : t) -> (y1 : t) -> (y2 : t) -> 
                               eq x1 x2 -> eq y1 y2 -> eq (op x1 y1) (op x2 y2)
                               
lift_bin_op_to_equal_pair : (setoid : Setoid) -> (op : BinaryOp (carrier setoid)) -> 
                                 (eq_respects_op : bin_op_respects_eq op (eq setoid)) -> BinaryOp (EqPair setoid)
lift_bin_op_to_equal_pair setoid op eq_respects_op (MkEqPair x1 x2 eq_x1_x2) (MkEqPair y1 y2 eq_y1_y2) =
  let op_x1_y1 = op x1 y1
      op_x2_y2 = op x2 y2
      eq_from_respect = eq_respects_op x1 x2 y1 y2 eq_x1_x2 eq_y1_y2
  in MkEqPair op_x1_y1 op_x2_y2 eq_from_respect
  
equal_pair_eq : (setoid : Setoid) -> (EqPair setoid) -> (EqPair setoid) -> Type
equal_pair_eq setoid (MkEqPair x1 x2 eq_x1_x2) (MkEqPair y1 y2 eq_y1_y2) = eq setoid x1 y1

equal_pairs_lifts_comm : (setoid : Setoid) -> (op : BinaryOp (carrier setoid)) -> CommutativeBy op (eq setoid) -> 
                         (eq_respects_op : bin_op_respects_eq op (eq setoid)) ->
                         CommutativeBy (lift_bin_op_to_equal_pair setoid op eq_respects_op) (equal_pair_eq setoid)
equal_pairs_lifts_comm setoid op comm_op_eq eq_respects_op (MkEqPair x1 x2 eq_x1_x2) (MkEqPair y1 y2 eq_y1_y2) = 
  comm_op_eq x1 y1

bin_op_respects_eq_left : (op : BinaryOp t) -> (eq : t -> t -> Type) -> Type
bin_op_respects_eq_left {t} op eq = (x1 : t) -> (x2 : t) -> (y : t) -> 
                               eq x1 x2 -> eq (op x1 y) (op x2 y)
                               
bin_op_respects_eq_right : (op : BinaryOp t) -> (eq : t -> t -> Type) -> Type
bin_op_respects_eq_right {t} op eq = (x : t) -> (y1 : t) -> (y2 : t) -> 
                               eq y1 y2 -> eq (op x y1) (op x y2)
                               
transitive : (eq : t -> t -> Type) -> Type
transitive {t} eq = {x : t} -> {y : t} -> {z : t} -> eq x y -> eq y z -> eq x z
                               
respect_eq_right_from_left_when_comm : bin_op_respects_eq_left op eq -> CommutativeBy op eq -> transitive eq -> 
                               bin_op_respects_eq_right op eq
respect_eq_right_from_left_when_comm {op} op_respects_eq_left comm_op_eq trans_eq x y1 y2 eq_y1_y2 = 
  let e1 = op_respects_eq_left y1 y2 x eq_y1_y2
      e2 = comm_op_eq x y1
      e3 = comm_op_eq y2 x
      e4 = trans_eq e1 e3
  in trans_eq e2 e4
  
bin_op_respect_eq_from_lr : {t: Type} -> (op : BinaryOp t) -> (eq : t -> t -> Type) -> transitive eq -> 
                             bin_op_respects_eq_left op eq -> bin_op_respects_eq_right op eq -> bin_op_respects_eq op eq
bin_op_respect_eq_from_lr {t} op eq transitive_eq respects_left respects_right x1 x2 y1 y2 eq_x1_x2 e1_y1_y2 = 
  let e1 = the (eq (op x1 y1) (op x2 y1)) $ respects_left x1 x2 y1 eq_x1_x2
      e2 = the (eq (op x2 y1) (op x2 y2)) $ respects_right x2 y1 y2 e1_y1_y2
  in transitive_eq e1 e2

respect_eq_from_left_when_comm : bin_op_respects_eq_left op eq -> CommutativeBy op eq -> transitive eq -> 
                               bin_op_respects_eq op eq
respect_eq_from_left_when_comm {op} {eq} op_respects_eq_left comm_op_eq trans_eq = 
  let op_respects_eq_right = respect_eq_right_from_left_when_comm op_respects_eq_left comm_op_eq trans_eq 
  in bin_op_respect_eq_from_lr op eq trans_eq op_respects_eq_left op_respects_eq_right

bin_op_respects_intensional_eq : (op : BinaryOp t) -> bin_op_respects_eq op (eq (IntensionalSetoid t))
bin_op_respects_intensional_eq {t} op x1 x2 y1 y2 eq_x1_x2 eq_y1_y2 = 
  let e1 = the (op x2 y2 = op x2 y2) Refl
  in rewrite eq_x1_x2 in rewrite eq_y1_y2 in e1

NatSetoid : Setoid
NatSetoid = IntensionalSetoid Nat
  
data Nat' : Type where
  MkNat' : EqPair NatSetoid -> Nat'
  
interface WrapsSetoid (t : Type) (setoid : Setoid) | t where
  wrap_pair : EqPair setoid -> t
  unwrap_pair : t -> EqPair setoid
  
WrapsSetoid Nat' NatSetoid where
  wrap_pair pair = MkNat' pair
  unwrap_pair (MkNat' pair) = pair
  
lift_bin_op_to_setoid_wrapper : WrapsSetoid t setoid => BinaryOp (EqPair setoid) -> BinaryOp t
lift_bin_op_to_setoid_wrapper op x y = wrap_pair $ op (unwrap_pair x) (unwrap_pair y)

lift_bin_op_to_intensional_equal_pair : (op : BinaryOp t) -> BinaryOp (EqPair (IntensionalSetoid t))
lift_bin_op_to_intensional_equal_pair {t} op = lift_bin_op_to_equal_pair (IntensionalSetoid t) op (bin_op_respects_intensional_eq op)
    
Num Nat' where
  (+) = lift_bin_op_to_setoid_wrapper (lift_bin_op_to_intensional_equal_pair {t=Nat} (+))
  (*) = lift_bin_op_to_setoid_wrapper (lift_bin_op_to_intensional_equal_pair {t=Nat} (*))
  fromInteger x = wrap_pair (identical_pair (fromInteger x))
  
nat'3 : Nat'
nat'3 = 3

double_nat : Nat -> Nat
double_nat x = x + x

lift_fun_to_intensional_eq : {setoid_t2 : Setoid} -> (f : t1 -> carrier setoid_t2) -> 
                         (EqPair (IntensionalSetoid t1) -> EqPair setoid_t2)
lift_fun_to_intensional_eq {setoid_t2} f (MkEqPair x y eq_x_y) = 
  MkEqPair (f x) (f y) eq_fx_fy where
     eq_fx_fy : eq setoid_t2 (f x) (f y)
     eq_fx_fy = 
       let x_is_y = the (x = y) eq_x_y
           fx_is_fy = cong {f=f} x_is_y
           eq_fy_fy = refl_eq setoid_t2
         in rewrite fx_is_fy in the (eq setoid_t2 (f y) (f y)) eq_fy_fy

data Integer_ : Type where
  MkInteger : (x : Nat) -> (y : Nat) -> Integer_
  
Num Integer_ where
  (MkInteger x1 x2) + (MkInteger y1 y2) = MkInteger (x1 + y1) (x2 + y2)
  (MkInteger x1 x2) * (MkInteger y1 y2) = MkInteger (x1 * y1 + x2 * y2) (x1 * y2 + x2 * y1)
  fromInteger x = if x < 0 
                     then MkInteger 0 (fromInteger (- x))
                     else MkInteger (fromInteger x) 0
                     
Integer_plus_comm : Commutative ((+) {ty=Integer_})
Integer_plus_comm (MkInteger x1 x2) (MkInteger y1 y2) = 
  let e1 = nat_lemmas.plus_comm x1 y1
      e2 = nat_lemmas.plus_comm x2 y2
  in rewrite e1 in rewrite e2 in Refl

Neg Integer_ where
  negate (MkInteger x1 x2) = MkInteger x2 x1
  (MkInteger x1 x2) - (MkInteger y1 y2) = MkInteger (x1 + y2) (x2 + y1)
  abs (MkInteger x1 x2) = if x1 > x2
                            then MkInteger x1 x2
                            else MkInteger x2 x1
  
IntegerSetoid : Setoid
IntegerSetoid = MkSetoid Integer_ int_eq int_refl_eq int_symm_eq int_trans_eq where
    int_eq : Integer_ -> Integer_ -> Type
    int_eq (MkInteger x1 x2) (MkInteger y1 y2) = x1 + y2 = x2 + y1

    int_refl_eq : {x : Integer_} -> int_eq x x
    int_refl_eq {x=MkInteger x1 x2} = nat_lemmas.plus_comm x1 x2

    int_symm_eq : {x : Integer_} -> {y : Integer_} -> int_eq x y -> int_eq y x
    int_symm_eq {x=MkInteger x1 x2} {y=MkInteger y1 y2} x_eq_y = 
      let e1 = the (y2 + x1 = x1 + y2) $ nat_lemmas.plus_comm y2 x1
          e2 = the (x2 + y1 = y1 + x2) $ nat_lemmas.plus_comm x2 y1
          e3 = the (x1 + y2 = x2 + y1) $ x_eq_y
       in sym $ trans e1 $ trans e3 e2
        
    int_trans_eq : {x : Integer_} -> {y : Integer_} -> {z : Integer_} -> 
                      int_eq x y -> int_eq y z -> int_eq x z
    int_trans_eq {x=MkInteger x1 x2} {y=MkInteger y1 y2} {z=MkInteger z1 z2} x_eq_y y_eq_z = 
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
      
abc_to_acb_lemma : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) + c = (a + c) + b
abc_to_acb_lemma a b c = 
  let e1 = the ((a + b) + c = a + (b + c)) $ nat_lemmas.plus_assoc a b c
      e2 = the (a + (c + b) = (a + c) + b) $ sym $ nat_lemmas.plus_assoc a c b
      e3 = the (b + c = c + b) $ nat_lemmas.plus_comm b c
      e4 = the (a + (b + c) = a + (c + b)) $ cong {f=\x => a + x} e3
  in trans e1 $ trans e4 e2

integer_plus_respects_eq : bin_op_respects_eq (+) (eq IntegerSetoid)                                                         
integer_plus_respects_eq (MkInteger w1 w2) (MkInteger x1 x2) (MkInteger y1 y2) (MkInteger z1 z2) eq_w_x eq_y_z = 
  let e1 = the ((w1 + y1) + (x2 + z2) = (w1 + x2) + (y1 + z2)) $ nat_lemmas.abcd_to_acbd_lemma w1 y1 x2 z2
      e2 = the ((w1 + x2) + (y1 + z2) = (w2 + x1) + (y1 + z2)) $ cong {f=\n => n + (y1 + z2)} eq_w_x
      e3 = the ((w2 + x1) + (y1 + z2) = (w2 + x1) + (y2 + z1)) $ cong {f=\n => (w2 + x1) + n} eq_y_z
  in trans e1 $ trans e2 $ trans e3 $ nat_lemmas.abcd_to_acbd_lemma w2 x1 y2 z1
  
combine_equalities : {x1 : t1} -> {y1 : t1} -> {x2 : t2} -> {y2 : t2} -> 
                            (f : t1 -> t2 -> t3) -> x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2
combine_equalities {x1} {y1} {x2} {y2} f x1_is_y1 x2_is_y2 = 
  let e1 = the (f x1 x2 = f y1 x2) $ cong {f=\z => f z x2} x1_is_y1
      e2 = the (f y1 x2 = f y1 y2) $ cong {f=\z => f y1 z} x2_is_y2
  in trans e1 e2
  
integer_times_respects_eq_left : bin_op_respects_eq_left (*) (eq IntegerSetoid)
integer_times_respects_eq_left (MkInteger x1 x2) (MkInteger y1 y2) (MkInteger z1 z2) int_eq_x_y = 
  let e1 = the ((x1 + y2) * z1 = (x2 + y1) * z1) $ cong {f=\s => s * z1} int_eq_x_y
      e2 = nat_lemmas.times_right_distr x1 y2 z1
      e3 = nat_lemmas.times_right_distr x2 y1 z1
      e4 = the (x1 * z1 + y2 * z1 = x2 * z1 + y1 * z1) $ trans (sym e2) $ trans e1 e3
      
      e5 = the ((x1 + y2) * z2 = (x2 + y1) * z2) $ cong {f=\s => s * z2} int_eq_x_y
      e6 = nat_lemmas.times_right_distr x1 y2 z2
      e7 = nat_lemmas.times_right_distr x2 y1 z2
      e8 = the (x2 * z2 + y1 * z2 = x1 * z2 + y2 * z2) $ trans (sym e7) $ trans (sym e5) e6
      
      e9 = the ((x1 * z1 + y2 * z1) + (x2 * z2 + y1 * z2) = (x2 * z1 + y1 * z1) + (x1 * z2 + y2 * z2)) 
                   $ combine_equalities (+) e4 e8
                   
      e10 = nat_lemmas.abcd_to_adbc_lemma (x1 * z1) (x2 * z2) (y1 * z2) (y2 * z1)
      e11 = nat_lemmas.abcd_to_cabd_lemma (x2 * z1) (y1 * z1) (x1 * z2) (y2 * z2)
  in the ((x1 * z1 + x2 * z2) + (y1 * z2 + y2 * z1) = (x1 * z2 + x2 * z1) + (y1 * z1 + y2 * z2)) 
             $ trans e10 $ trans e9 e11

integer_times_respects_eq_right : bin_op_respects_eq_right (*) (eq IntegerSetoid)
integer_times_respects_eq_right = ?right

integer_times_respects_eq : bin_op_respects_eq (*) (eq IntegerSetoid)                                                         
integer_times_respects_eq = bin_op_respect_eq_from_lr (*) (eq IntegerSetoid) (trans_eq IntegerSetoid) 
                                 integer_times_respects_eq_left integer_times_respects_eq_right

data Integer' : Type where
  MkInteger' : EqPair IntegerSetoid -> Integer'
  
WrapsSetoid Integer' IntegerSetoid where
  wrap_pair pair = MkInteger' pair
  unwrap_pair (MkInteger' pair) = pair
  
Num Integer' where
  (+) = lift_bin_op_to_setoid_wrapper (lift_bin_op_to_equal_pair IntegerSetoid (+) integer_plus_respects_eq)
  (*) = lift_bin_op_to_setoid_wrapper (lift_bin_op_to_equal_pair IntegerSetoid (*) integer_times_respects_eq)
  fromInteger x = wrap_pair (identical_pair (fromInteger x))

Integer'3 : Integer'
Integer'3 = 3
