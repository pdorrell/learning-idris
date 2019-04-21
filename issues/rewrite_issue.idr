%default total

data Parity = Even | Odd

data ABC = A | B | C

-- a contrived example of using rewrite, that works OK
rewrite_example: (x = A, y = (Even, B)) -> (z = (Even, B)) -> (x = A, y = z)
rewrite_example {x} {y} {z} x_is_A_and_y_is_even_and_b z_is_even_and_b = 
  the (x = A, y = z) $ rewrite z_is_even_and_b in x_is_A_and_y_is_even_and_b
  
-- a 2nd example of rewrite, where only one (Even, B) of two needs to be rewritten
rewrite_example2: (x = (A, (Even, B)), y = (Even, B)) -> (z = (Even, B)) -> (x = (A, (Even, B)), y = z)
rewrite_example2 {x} {y} {z} x_prf_and_y_is_even_and_b z_is_even_and_b = 
  the (x = (A, (Even, B)), y = z) $ rewrite z_is_even_and_b in x_prf_and_y_is_even_and_b
  
Opposite: Parity -> Parity
Opposite Even = Odd
Opposite Odd = Even

ParityOf: (n : Nat) -> Parity
ParityOf Z = Even
ParityOf (S k) = Opposite $ ParityOf k

-- this works, because it works when function applications are automatically applied
lemma3 : (n : Nat) -> Even = ParityOf n -> Odd = ParityOf (S n)
lemma3 n n_is_even =
   let e1 = the (Odd = Opposite Even) $ Refl
   in rewrite sym n_is_even in e1

-- using a cong instead of write, it works
lemma1 : (n : Nat) -> Even = ParityOf n -> Odd = ParityOf (S n)
lemma1 n n_is_even =
  let e1 = the (ParityOf (S n) = Opposite (ParityOf n)) Refl
      e2 = the (Opposite Even = Opposite $ ParityOf n) $ cong n_is_even
      e3 = the (ParityOf (S n) = Opposite Even) $ trans e1 $ sym e2
      e4 = the (Odd = ParityOf (S n)) $ sym e3
  in e4

-- using a rewrite, it doesn't work
lemma2 : (n : Nat) -> Even = ParityOf n -> Odd = ParityOf (S n)
lemma2 n n_is_even =
  let e1 = the (ParityOf (S n) = Opposite (ParityOf n)) Refl
      e2 = the (ParityOf (S n) = Opposite Even) $ ?h1 -- rewrite n_is_even in e1
      e4 = the (Odd = ParityOf (S n)) $ sym e2
  in ?hole2

