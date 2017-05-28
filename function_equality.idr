%default total

id_equal_to_self: id = id
id_equal_to_self = Refl

fun1 : Nat -> Nat
fun1 n = n + 2

fun2 : Nat -> Nat
fun2 n = n + 2

fun3 : Nat -> Nat
fun3 n = (n + 1) + 1

fun1_equal_to_fun1 : Main.fun1 = Main.fun1
fun1_equal_to_fun1 = Refl

fun1_equal_to_fun2 : Main.fun1 = Main.fun2
fun1_equal_to_fun2 = Refl

fun1_not_equal_to_fun3 : Main.fun1 = Main.fun3 -> Void
fun1_not_equal_to_fun3 Refl impossible

fun1_same_results_as_fun3: (n : Nat) -> fun1 n = fun3 n
fun1_same_results_as_fun3 Z = Refl
fun1_same_results_as_fun3 (S k) = cong {f=S} $ fun1_same_results_as_fun3 k

functions_have_same_results: {t1 : Type} -> {t2 : Type} -> (f1 : t1 -> t2) -> (f2 : t1 -> t2) -> Type
functions_have_same_results {t1} {t2} f1 f2 = (x : t1) -> f1 x = f2 x

fun1_fun3_are_equal : functions_have_same_results Main.fun1 Main.fun3
fun1_fun3_are_equal = fun1_same_results_as_fun3

fun_respects_eq : Eq t1 => Eq t2 => {t1 : Type} -> {t2 : Type} -> (f1 : t1 -> t2) -> (f2 : t1 -> t2) -> Type
fun_respects_eq {t1} {t2} f1 f2 = (x : t1) -> (y : t1) -> ((x == y) = True) -> ?hole -- ((f1 x) == (f2 x)) = True


one_equal_to_two: 1 = 2 -> Void
one_equal_to_two Refl impossible
