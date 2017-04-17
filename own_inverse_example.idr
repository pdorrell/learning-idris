%default total

-- The type of parity values - either Even or Odd
data Parity = Even | Odd

-- Even is the opposite of Odd and Odd is the opposite of Even
opposite: Parity -> Parity
opposite Even = Odd
opposite Odd  = Even

-- The 'opposite' function is it's own inverse
opposite_its_own_inverse : (p : Parity) -> opposite (opposite p) = p
opposite_its_own_inverse Even = Refl
opposite_its_own_inverse Odd  = Refl

-- abstraction of being one's own inverse

IsItsOwnInverse : {t : Type} -> (f: t->t) -> Type
IsItsOwnInverse {t} f = (x: t) -> f (f x) = x

opposite_IsItsOwnInverse : IsItsOwnInverse {t=Parity} Main.opposite
opposite_IsItsOwnInverse = opposite_its_own_inverse

-- implicit {t=Parity} can be left out
opposite_IsItsOwnInverse2 : IsItsOwnInverse Main.opposite
opposite_IsItsOwnInverse2 = opposite_its_own_inverse

-- Or do the whole proof in one step
opposite_IsItsOwnInverse3 : IsItsOwnInverse Main.opposite
opposite_IsItsOwnInverse3 Even = Refl
opposite_IsItsOwnInverse3 Odd = Refl

-- The last definition fails with 'Type mismatch between opposite (opposite v0) and opposite (opposite v0)'
