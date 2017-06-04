%default total

[default_eq] Eq a where
  (==) = (==) @{jim}

extract_constraint: (eqa : Eq a) => Eq a
extract_constraint {a} = ?hole

eq_example: Eq Nat
eq_example = extract_constraint {a=Nat}
