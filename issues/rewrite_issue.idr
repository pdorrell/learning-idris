%default total

data Parity = Even | Odd

data ABC = A | B | C

-- a contrived example of using rewrite, that works OK
rewrite_example: (x = A, y = (Even, B)) -> (z = (Even, B)) -> (x = A, y = z)
rewrite_example {x} {y} {z} x_is_A_and_y_is_even_and_b z_is_even_and_b = 
  the (x = A, y = z) $ rewrite z_is_even_and_b in x_is_A_and_y_is_even_and_b
  
Opposite: Parity -> Parity
Opposite Even = Odd
Opposite Odd = Even

ParityOf: (n : Nat) -> Parity
ParityOf Z = Even
ParityOf (S k) = Opposite $ ParityOf k

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
      e2 = the (ParityOf (S n) = Opposite Even) $ ?hole -- rewrite n_is_even in e1
      e4 = the (Odd = ParityOf (S n)) $ sym e2
  in e4
