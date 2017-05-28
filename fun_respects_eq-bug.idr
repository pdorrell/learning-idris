%default total

fun_respects_eq : (Eq t1, Eq t2) => {t1 : Type} -> {t2 : Type} -> (f : t1 -> t2) -> Type
fun_respects_eq {t1} {t2} f = (x : t1) -> (y : t1) -> x == y = True -> ?hole -- f x == f y = True

fun_respects_eq2 : (Eq t1, Eq t2) => (f : t1 -> t2) -> Type
fun_respects_eq2 {t1} {t2} f = (x : t1) -> (y : t1) -> x == y = True -> ?hole2 -- f x == f y = True
