module Stability

%default total

public export
data Stable : Type -> Type where
  ProveFromDoubleNeg : {prop : Type} -> (((prop -> Void) -> Void) -> prop) -> Stable prop

prop_implies_not_not_prop : {prop : Type} -> prop -> Not (Not prop)
prop_implies_not_not_prop p not_p = not_p p

negations_are_stable : (prop : Type) -> Stable (Not prop)
negations_are_stable prop = ProveFromDoubleNeg not_not_not_prop_implies_not_prop where
  not_not_not_prop_implies_not_prop : Not (Not (Not prop)) -> Not prop
  not_not_not_prop_implies_not_prop not_not_not_prop p = 
    let not_not_prop = prop_implies_not_not_prop p in
      not_not_not_prop not_not_prop

public export
dec_implies_stable : Dec prop -> Stable prop
dec_implies_stable (Yes prop_is_true) = ProveFromDoubleNeg not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = prop_is_true
dec_implies_stable (No prop_is_not_true) = ProveFromDoubleNeg not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = void $ not_not_p prop_is_not_true
