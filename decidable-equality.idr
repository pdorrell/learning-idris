
data ProvableFromDoubleNeg : Type -> Type where
  ProveFromDoubleNeg : (prop : Type) -> (((prop -> Void) -> Void) -> prop) -> ProvableFromDoubleNeg prop
  
DecImpliesProvableFromDoubleNeg : Dec prop -> ProvableFromDoubleNeg prop
DecImpliesProvableFromDoubleNeg (Yes prop_is_true) = ProveFromDoubleNeg prop not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = prop_is_true
DecImpliesProvableFromDoubleNeg (No prop_is_not_true) = ProveFromDoubleNeg prop not_not_p_implies_p where
  not_not_p_implies_p : ((prop -> Void) -> Void) -> prop
  not_not_p_implies_p not_not_p = void $ not_not_p prop_is_not_true
  
not_not_equals_implies_equals_from_dec : DecEq t => {x : t} -> {y : t} -> ((x = y -> Void) -> Void) -> x = y
not_not_equals_implies_equals_from_dec {x} {y} x_is_not_not_y with (decEq x y)
  | Yes x_is_y = x_is_y
  | No x_is_not_y = void $ x_is_not_not_y x_is_not_y


not_not_dec_from_not_not_equals_implies_equals : {x : t} -> {y : t} -> (((x = y -> Void) -> Void) -> x = y) -> (Dec(x = y) -> Void) -> Void
not_not_dec_from_not_not_equals_implies_equals {x} {y} x_is_not_not_y_implies_x_is_y x_is_y_not_dec = 
  let when_x_is_y = \if_x_is_y => Yes $ the (x = y) if_x_is_y in
  let when_x_is_not_y = \if_x_is_not_y => No $ the (x = y -> Void) if_x_is_not_y in
  let x_is_not_y = x_is_y_not_dec . when_x_is_y in
  let x_is_y_dec = when_x_is_not_y x_is_not_y in 
    x_is_y_not_dec x_is_y_dec

dec_from_not_not_equals_implies_equals : {x : t} -> {y : t} -> (((x = y -> Void) -> Void) -> x = y) -> Dec(x = y)
dec_from_not_not_equals_implies_equals {x} {y} x_is_not_not_y_implies_x_is_y = 
  let when_x_is_y = \if_x_is_y => Yes $ the (x = y) if_x_is_y in
  let when_x_is_not_y = \if_x_is_not_y => No $ the (x = y -> Void) if_x_is_not_y in
  ?hole
