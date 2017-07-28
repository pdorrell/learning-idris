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
    let e1 = the (S (y + k) = y + S k) $  s_on_right_addend y k
        e2 = the (S (k + y) = S (y + k)) $ cong {f=S} $ plus_commutative k y
    in the (S (k + y) = y + S k) $ trans e2 e1

  plus_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x + y) + z = x + (y + z)
  plus_assoc Z y z = Refl
  plus_assoc (S k) y z = ?plus_assoc_rhs_2
