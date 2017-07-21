

idris_not_php : 2 = "2"
idris_not_php = ?hole

--the (the String 2 = "2") Refl

Num String where
  (+) x y = y
  (*) x y = y
  fromInteger n = "2"
  
--idris_not_php2 : S (S Z) = "2"
--idris_not_php2 = ?hole
  

idris_not_php3 : S (S Z) ~=~ "2"
idris_not_php3 = ?hole
