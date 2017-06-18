%default total

data ProvableFromDoubleNeg : Type -> Type where
  ProveFromDoubleNeg : {prop : Type} -> (((prop -> Void) -> Void) -> prop) -> ProvableFromDoubleNeg prop
  
prop_implies_not_not_prop : {prop : Type} -> prop -> Not (Not prop)
prop_implies_not_not_prop p not_p = not_p p

-- (constructive) law of contrapositive
contrapositive: (prop1 -> prop2) -> (Not prop2 -> Not prop1)
contrapositive prop1_implies_prop2 not_prop2 prop1_prf = not_prop2 $ prop1_implies_prop2 $ prop1_prf

negations_provable_from_double_neg : (prop : Type) -> ProvableFromDoubleNeg (Not prop)
negations_provable_from_double_neg prop = ProveFromDoubleNeg not_not_not_prop_implies_not_prop where
  not_not_not_prop_implies_not_prop : Not (Not (Not prop)) -> Not prop
  not_not_not_prop_implies_not_prop not_not_not_prop p = 
    let not_not_prop = prop_implies_not_not_prop p in
      not_not_not_prop not_not_prop


DecImpliesProvableFromDoubleNeg : Dec prop -> ProvableFromDoubleNeg prop
DecImpliesProvableFromDoubleNeg (Yes prop_is_true) = ProveFromDoubleNeg not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = prop_is_true
DecImpliesProvableFromDoubleNeg (No prop_is_not_true) = ProveFromDoubleNeg not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = void $ not_not_p prop_is_not_true
  
not_not_equals_implies_equals_from_dec : DecEq t => {x : t} -> {y : t} -> ((x = y -> Void) -> Void) -> x = y
not_not_equals_implies_equals_from_dec {x} {y} x_is_not_not_y with (decEq x y)
  | Yes x_is_y = x_is_y
  | No x_is_not_y = void $ x_is_not_not_y x_is_not_y


not_not_dec_x_is_y : {x : t} -> {y : t} -> Not (Not (Dec(x = y)))
not_not_dec_x_is_y {x} {y} x_is_y_not_dec = 
  let when_x_is_y = \if_x_is_y => Yes $ the (x = y) if_x_is_y in
  let when_x_is_not_y = \if_x_is_not_y => No $ the (x = y -> Void) if_x_is_not_y in
  let x_is_not_y = x_is_y_not_dec . when_x_is_y in
  let x_is_y_dec = when_x_is_not_y x_is_not_y in 
    x_is_y_not_dec x_is_y_dec

dec_from_not_not_equals_implies_equals : {x : t} -> {y : t} -> ProvableFromDoubleNeg(x = y) -> Dec(x = y)
dec_from_not_not_equals_implies_equals {x} {y} (ProveFromDoubleNeg x_is_not_not_y_implies_x_is_y) = 
  let when_x_is_y = \if_x_is_y => Yes $ the (x = y) if_x_is_y in
  let when_x_is_not_y = \if_x_is_not_y => No $ the (x = y -> Void) if_x_is_not_y in
  let when_x_is_not_not_y = when_x_is_y . x_is_not_not_y_implies_x_is_y in
  ?hole
