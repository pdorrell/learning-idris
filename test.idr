module Main

plusAssoc : (l, c, r : Nat) -> l `plus` (c `plus` r ) = (l `plus` c) `plus` r
plusAssoc Z     c r = Refl
plusAssoc (S l) c r = rewrite plusAssoc l c r in Refl

plusAssoc2 : (l, c, r : Nat) -> l `plus` (c `plus` r ) = (l `plus` c) `plus` r
plusAssoc2 l c r = ?plusAssoc2_rhs

plusAssoc3 : (l, c, r : Nat) -> l `plus` (c `plus` r ) = (l `plus` c) `plus` r
plusAssoc3 Z     c r = Refl
plusAssoc3 (S l) c r = ?plusAssoc3_rhs_2


---------- Proofs ----------
Main.plusAssoc3_rhs_2 = proof
  intros
  rewrite plusAssoc3 l c r
  trivial
  
Main.plusAssoc2_rhs = proof
  intros
  induction l
  compute
  trivial
  intros
  compute
  rewrite ihn__0
  trivial


