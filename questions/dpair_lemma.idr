%default total

-- Prove first elements of two equal dependent pairs are equal
dpair_fst_lemma : {t : Type} -> {P : t -> Type} -> {x1, x2 : t} -> {y1 : P x1} -> {y2 : P x2} 
                       -> (x1 ** y1) = (x2 ** y2) -> x1 = x2
dpair_fst_lemma {P} {x1} {x2} {y1} {y2} x1_y1_eq_x2_y2 = cong {f=DPair.fst} x1_y1_eq_x2_y2

-- Trying to prove second elements of two equal dependent pairs are equal
dpair_lemma : {t : Type} -> {P : t -> Type} -> {x : t} -> {y1, y2 : P x} 
                       -> (x ** y1) = (x ** y2) -> y1 = y2
dpair_lemma {P} {x} {y1} {y2} x_y1_eq_x_y2  = cong {f=DPair.snd} x_y1_eq_x_y2

-- Trying to prove second elements of two equal dependent pairs are equal, special case where first elements are True:Bool
true_dpair_lemma : {P : Bool -> Type} -> {y1, y2 : P True} -> (True ** y1) = (True ** y2) -> y1 = y2
true_dpair_lemma {P} {y1} {y2} pair1_eq_pair2 = cong {f=DPair.snd} pair1_eq_pair2
