%default total

dpair_lemma : {t : Type} -> {P : t -> Type} -> {x : t} -> {y1, y2 : P x} -> (x ** y1) = (x ** y2) -> y1 = y2
dpair_lemma {P} {x} {y1} {y2} x_y1_eq_x_y2  = ?dpair_lemma_rhs

true_dpair_lemma : {P : Bool -> Type} -> {y1, y2 : P True} -> (True ** y1) = (True ** y2) -> y1 = y2
true_dpair_lemma {P} {y1} {y2} pair1_eq_pair2 = ?true_dpair_lemma_rhs

false_dpair_lemma : {P : Bool -> Type} -> {y1, y2 : P False} -> (False ** y1) = (False ** y2) -> y1 = y2
false_dpair_lemma {P} {y1} {y2} pair1_eq_pair2 = ?false_dpair_lemma_rhs

bool_dpair_lemma : {P : Bool -> Type} -> {x : Bool} -> {y1, y2 : P x} -> (x ** y1) = (x ** y2) -> y1 = y2
bool_dpair_lemma {P} {x=True} {y1} {y2} x_y1_eq_x_y2 = true_dpair_lemma {P} {y1} {y2} x_y1_eq_x_y2
bool_dpair_lemma {P} {x=False} {y1} {y2} x_y1_eq_x_y2 = false_dpair_lemma {P} {y1} {y2} x_y1_eq_x_y2

dpair_fst_lemma : {t : Type} -> {P : t -> Type} -> {x1, x2 : t} -> {y1 : P x1} -> {y2 : P x2} -> (x1 ** y1) = (x2 ** y2) -> x1 = x2
dpair_fst_lemma {P} {x1} {x2} {y1} {y2} x1_y1_eq_x2_y2 = cong {f=DPair.fst} x1_y1_eq_x2_y2
