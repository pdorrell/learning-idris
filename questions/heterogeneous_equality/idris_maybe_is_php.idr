Num String where
  (+) x y = y
  (*) x y = y
  fromInteger n = "2"

Two_string_equals_type : Type
Two_string_equals_type = the String 2 = "2"

idris_not_php : Two_string_equals_type
idris_not_php = Refl
