
not_not_equals : DecEq t => {x : t} -> {y : t} -> ((x = y -> Void) -> Void) -> x = y
not_not_equals {x} {y} x_is_not_not_y with (decEq x y)
  | Yes x_is_y = x_is_y
  | No x_is_not_y = void $ x_is_not_not_y x_is_not_y
