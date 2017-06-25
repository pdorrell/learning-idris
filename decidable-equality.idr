%default total

data Stable : Type -> Type where
  ProveFromDoubleNeg : {prop : Type} -> (((prop -> Void) -> Void) -> prop) -> Stable prop
  
prop_implies_not_not_prop : {prop : Type} -> prop -> Not (Not prop)
prop_implies_not_not_prop p not_p = not_p p

-- (constructive) law of contrapositive
contrapositive: (prop1 -> prop2) -> (Not prop2 -> Not prop1)
contrapositive prop1_implies_prop2 not_prop2 prop1_prf = not_prop2 $ prop1_implies_prop2 $ prop1_prf

negations_are_stable : (prop : Type) -> Stable (Not prop)
negations_are_stable prop = ProveFromDoubleNeg not_not_not_prop_implies_not_prop where
  not_not_not_prop_implies_not_prop : Not (Not (Not prop)) -> Not prop
  not_not_not_prop_implies_not_prop not_not_not_prop p = 
    let not_not_prop = prop_implies_not_not_prop p in
      not_not_not_prop not_not_prop

dec_implies_stable : Dec prop -> Stable prop
dec_implies_stable (Yes prop_is_true) = ProveFromDoubleNeg not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = prop_is_true
dec_implies_stable (No prop_is_not_true) = ProveFromDoubleNeg not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = void $ not_not_p prop_is_not_true

-- for any proposition prop, it is not true that prop is not decidable.
not_not_dec_prop : {prop : Type} -> Not (Not (Dec prop))
not_not_dec_prop {prop} not_dec_prop = 
  let not_prop = not_dec_prop . Yes in
  let dec_prop = No not_prop in
    not_dec_prop dec_prop
    
not_all_props_are_dec : (prop : Type -> Dec prop) -> Void
not_all_props_are_dec all_props_are_dec = 
--  let dec_prop = all_props_are_dec prop in
    ?not_all_props_are_dec_rhs

-- probably this isn't provable, because it effectively says
-- that if a proposition is classically True, then it is decidable
dec_from_not_not_prop_implies_prop : {prop : Type} -> Stable prop -> Dec prop
dec_from_not_not_prop_implies_prop {prop} (ProveFromDoubleNeg not_not_p_implies_p) = 
  let when_p = \p => Yes $ the prop p in
  let when_not_p = \not_p => No $ the (Not prop) not_p in
  let when_not_not_p = when_p . not_not_p_implies_p in
  ?hole
