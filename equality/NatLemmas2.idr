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
    
  times_zero : (x : Nat) -> x * 0 = 0
  times_zero Z = Refl
  times_zero (S k) = rewrite times_zero k in Refl
  
  times_S_x : (x : Nat) -> (y : Nat) -> y + y * x = y * S x
  times_S_x x Z = Refl
  times_S_x x (S k) = 
    let e1 = the (k + (x + k * x) = k + x + k * x) $ sym $ plus_assoc k x (k * x)
        e2 = the (k + x + k * x = x + k + k * x) $ rewrite plus_comm k x in Refl
        e3 = the (x + k + k * x = x + (k + k * x)) $ plus_assoc x k (k * x)
        e4 = the (x + (k + k * x) = x + (k * S x)) $ cong {f=\z => x + z} $ times_S_x x k
        e5 = the (k + (x + k * x) = x + k * S x) $ trans e1 $ trans e2 $ trans e3 e4
    in cong {f=S} $ the (k + (x + k * x) = x + (k * S x)) $ e5
  
  times_comm_S : (x : Nat) -> (y : Nat) -> x * y = y * x -> S x * y = y * S x
  times_comm_S x y times_comm_x_y = 
    rewrite times_comm_x_y in times_S_x x y
  
  times_comm : (x : Nat) -> (y : Nat) -> x * y = y * x
  times_comm Z y = sym $ times_zero y
  times_comm (S k) y = times_comm_S k y (times_comm k y)
