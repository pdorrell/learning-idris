%default total

id_equal_to_self: Basics.id = Basics.id
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

fun_respects_eq : (Eq t1, Eq t2) => (f : t1 -> t2) -> Type
fun_respects_eq {t1} {t2} f = (x : t1) -> (y : t1) -> x == y = True -> f x == f y = True

lemma2 : (x: Nat) -> (y: Nat) -> S x = S y -> x = y
lemma2 y y Refl = Refl

nat_eq_implies_equals : (x: Nat) -> (y: Nat) -> x == y = True -> x = y
nat_eq_implies_equals Z Z prf = Refl
nat_eq_implies_equals Z (S _) Refl impossible
nat_eq_implies_equals (S _) Z Refl impossible
nat_eq_implies_equals (S k) (S j) prf = rewrite nat_eq_implies_equals k j prf in Refl

nat_eq_is_symmetric : (x: Nat) -> x == x = True
nat_eq_is_symmetric Z = Refl
nat_eq_is_symmetric (S k) = nat_eq_is_symmetric k

nat_eq_is_reflexive : (x: Nat) -> (y: Nat) -> x = y -> x == y = True
nat_eq_is_reflexive y y Refl = nat_eq_is_symmetric y

fun1_respects_eq : fun_respects_eq {t1=Nat} {t2=Nat} Main.fun1
fun1_respects_eq x y x_eq_y = 
      let x_equals_y = nat_eq_implies_equals x y x_eq_y in
      let fun1_x_equals_fun1_y = cong {f=Main.fun1} x_equals_y in 
      nat_eq_is_reflexive (Main.fun1 x) (Main.fun1 y) fun1_x_equals_fun1_y

  
functions_are_eq: (Eq t1, Eq t2) => (f1 : t1 -> t2) -> (f2 : t1 -> t2) -> Type
functions_are_eq {t1} {t2} f1 f2 = (x : t1) -> (y : t1) -> x==y = True -> f1 x == f2 y = True

one_equal_to_two: 1 = 2 -> Void
one_equal_to_two Refl impossible
