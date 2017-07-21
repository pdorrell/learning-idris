Num String where
  (+) x y = y
  (*) x y = y
  fromInteger n = "2"

idris_not_php : 2 ~=~ "2"
idris_not_php = the (the String 2 = "2") Refl
