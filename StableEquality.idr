module StableEquality

import Stability

%default total

data EqualityIsStable : Type -> Type where
  ProveIsStable : ((x : t) -> (y : t) -> Stable (x = y)) -> EqualityIsStable t
  
falseNotTrue : False = True -> Void
falseNotTrue = negEqSym trueNotFalse

bool_equality_is_stable : EqualityIsStable Bool
bool_equality_is_stable = ProveIsStable $ bool_x_is_y_is_stable where
  bool_x_is_y_is_stable : (x : Bool) -> (y : Bool) -> Stable (x = y)
  bool_x_is_y_is_stable False False = ProveFromDoubleNeg $ const Refl
  bool_x_is_y_is_stable False True = ProveFromDoubleNeg $ \f_is_not_not_t => void $ f_is_not_not_t falseNotTrue
  bool_x_is_y_is_stable True False = ProveFromDoubleNeg $ \t_is_not_not_f => void $ t_is_not_not_f trueNotFalse
  bool_x_is_y_is_stable True True = ProveFromDoubleNeg $ const Refl
  
dec_eq_implies_stable_eq : DecEq t => EqualityIsStable t
dec_eq_implies_stable_eq = ProveIsStable dec_eq_stable_lemma where
  dec_eq_stable_lemma : DecEq t => (x : t) -> (y : t) -> Stable (x = y)
  dec_eq_stable_lemma x y = dec_implies_stable $ decEq x y

zeroNotSucc : (n : Nat) -> Z = S(n) -> Void
zeroNotSucc _ Refl impossible

nat_equality_is_stable : EqualityIsStable Nat
nat_equality_is_stable = dec_eq_implies_stable_eq {t=Nat}
