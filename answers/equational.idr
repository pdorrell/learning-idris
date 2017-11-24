%default total

plus_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x + y) + z = x + (y + z)

plus_comm : (x : Nat) -> (y : Nat) -> x + y = y + x

abcd_to_acbd_lemma : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> 
                (a + b) + (c + d) = (a + c) + (b + d)
abcd_to_acbd_lemma a b c d = 
    let e1 = the ((a + b) + (c + d) = ((a + b) + c) + d) $ sym (plus_assoc (a + b) c d)
        e2 = the (((a + b) + c) + d = (a + (b + c)) + d) $ rewrite (plus_assoc a b c) in Refl
        e3 = the ((a + (b + c)) + d = (a + (c + b)) + d) $ rewrite (plus_comm b c) in Refl
        e4 = the ((a + (c + b)) + d = ((a + c) + b) + d) $ rewrite (plus_assoc a c b) in Refl
        e5 = the ((((a + c) + b) + d) = (a + c) + (b + d)) $ plus_assoc (a + c) b d
    in trans e1 $ trans e2 $ trans e3 $ trans e4 e5
