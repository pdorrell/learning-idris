module NatLemmas

%access public export

namespace nat_lemmas
  zero_right_ident : (x : Nat) -> x = x + 0
  zero_right_ident Z = Refl
  zero_right_ident (S k) = rewrite zero_right_ident k in Refl
  
  s_on_right_addend : (x : Nat) -> (y : Nat) -> S (x + y) = x + S y
  s_on_right_addend Z y = Refl
  s_on_right_addend (S k) y = rewrite s_on_right_addend k y in Refl

  plus_comm : (x : Nat) -> (y : Nat) -> x + y = y + x
  plus_comm Z y = zero_right_ident y
  plus_comm (S k) y =
    let e1 = the (S (y + k) = y + S k) $  s_on_right_addend y k
        e2 = the (S (k + y) = S (y + k)) $ cong {f=S} $ plus_comm k y
    in the (S (k + y) = y + S k) $ trans e2 e1

  plus_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x + y) + z = x + (y + z)
  plus_assoc Z y z = Refl
  plus_assoc (S k) y z = cong {f=S} $ plus_assoc k y z
  
  cancel_s : (x : Nat) -> (y : Nat) -> S x = S y -> x = y
  cancel_s x _ Refl = Refl
  
  abcd_to_acbd_lemma : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> 
                (a + b) + (c + d) = (a + c) + (b + d)
  abcd_to_acbd_lemma a b c d = 
    let e1 = the ((a + b) + (c + d) = ((a + b) + c) + d) $ sym (plus_assoc (a + b) c d)
        e2 = the (((a + b) + c) + d = (a + (b + c)) + d) $ rewrite (plus_assoc a b c) in Refl
        e3 = the ((a + (b + c)) + d = (a + (c + b)) + d) $ rewrite (plus_comm b c) in Refl
        e4 = the ((a + (c + b)) + d = ((a + c) + b) + d) $ rewrite (plus_assoc a c b) in Refl
        e5 = the ((((a + c) + b) + d) = (a + c) + (b + d)) $ plus_assoc (a + c) b d
    in trans e1 $ trans e2 $ trans e3 $ trans e4 e5

  plus_left_cancel : (x : Nat) -> (y : Nat) -> (z : Nat) -> z + x = z + y -> x = y
  plus_left_cancel x y Z z_plus_x_is_z_plus_y = z_plus_x_is_z_plus_y
  plus_left_cancel x y (S k) z_plus_x_is_z_plus_y = 
    let e1 = the (S (k + x) = S (k + y)) z_plus_x_is_z_plus_y
        e2 = the (k + x = k + y) $ cancel_s (k + x) (k + y) e1
    in plus_left_cancel x y k e2
  
  plus_right_cancel : (x : Nat) -> (y : Nat) -> (z : Nat) -> x + z = y + z -> x = y
  plus_right_cancel x y z x_plus_z_is_y_plus_z = 
    let e1 = the (z + x = z + y) $ trans (plus_comm z x) (trans x_plus_z_is_y_plus_z (plus_comm y z))
    in plus_left_cancel x y z e1

  times_left_distr : (x : Nat) -> (y : Nat) -> (z : Nat) -> z * (x + y) = (z * x) + (z * y)
  times_left_distr x y Z = Refl
  times_left_distr x y (S k) = 
    let e1 = the (k * (x + y) = k * x + k * y) $ times_left_distr x y k
        e2 = the ((x + y) + (k * (x + y)) = (x + y) + (k * x + k * y)) $ rewrite e1 in Refl
        e3 = the ((x + y) + (k * x + k * y) = (x + k * x) + (y + k * y)) $ abcd_to_acbd_lemma x y (k * x) (k * y)
    in the ((x + y) + (k * (x + y)) = (x + (k * x)) + (y + (k * y))) $ trans e2 e3

  times_right_distr : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x + y) * z = (x * z) + (y * z)
  times_right_distr x y z = ?rhs
