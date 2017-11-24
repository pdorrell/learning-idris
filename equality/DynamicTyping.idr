
data Dynamic : Type where
  Nat : Nat -> Dynamic
  Bool : Bool -> Dynamic
  String : String -> Dynamic
  List : List Dynamic -> Dynamic
  Error : List Dynamic -> Dynamic
  
get_nat : Dynamic -> Maybe Nat
get_nat (Nat k) = Just k
get_nat _ = Nothing

maybe_nat_plus : Maybe Nat -> Maybe Nat -> Maybe Nat
maybe_nat_plus Nothing y = Nothing
maybe_nat_plus (Just x) Nothing = Nothing
maybe_nat_plus (Just x) (Just y) = Just (x + y)

example_3 : Dynamic
example_3 = Nat 3

example_list : Dynamic
example_list = List [Nat 3, Bool True]

example_list2 : Dynamic
example_list2 = List [Nat 3, Nat 5]

nat_plus : Dynamic -> Dynamic -> Dynamic


nat_sum : Dynamic -> Dynamic

