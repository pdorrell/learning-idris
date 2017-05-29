%default total

unconstrained_no_implicit_declaration: (f : t1 -> t2) -> Type
unconstrained_no_implicit_declaration {t1} {t2} f = (x : t1) -> (y : t1) -> x = y -> ?unc_no_imp_rhs

unconstrained_implicit_declaration: {t1 : Type} -> {t2 : Type} -> (f : t1 -> t2) -> Type
unconstrained_implicit_declaration {t1} {t2} f = (x : t1) -> (y : t1) -> x = y -> ?unc_imp_rhs

constrained_no_implicit_declaration : (Eq t1, Eq t2) => (f : t1 -> t2) -> Type
constrained_no_implicit_declaration {t1} {t2} f = (x : t1) -> (y : t1) -> x = y -> ?cons_no_imp_rhs

constrained_implicit_declaration : (Eq t1, Eq t2) => {t1 : Type} -> {t2 : Type} -> (f : t1 -> t2) -> Type
constrained_implicit_declaration {t1} {t2} f = (x : t1) -> (y : t1) -> x = y -> ?cons_imp_rhs
