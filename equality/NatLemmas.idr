module NatLemmas

%access public export

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
