module EqualityInterfaces

%default total

interface Eq t => LawfulEq t where
  eq_is_reflexive : (x : t) -> x == x = True
  eq_is_symmetric : (x : t) -> (y : t) -> x == y = y == x
  eq_is_transitive : (x : t) -> (y : t) -> (z : t) -> x == y = True -> x == z = y == z
  
interface Canonical t where
  canonical : t -> t
  canonical_is_idempotent : (x : t) -> canonical (canonical x) = canonical x
  
namespace bool_equality_lemmas
  
  reflexive : (x : Bool) -> x == x = True
  reflexive False = Refl
  reflexive True = Refl

  symmetric : (x : Bool) -> (y : Bool) -> x == y = y == x
  symmetric False False = Refl
  symmetric False True = Refl
  symmetric True False = Refl
  symmetric True True = Refl

  transitive : (x : Bool) -> (y : Bool) -> (z : Bool) -> x == y = True -> x == z = y == z
  transitive False False z Refl = Refl
  transitive False True _ Refl impossible
  transitive True False _ Refl impossible
  transitive True True z Refl = Refl
  
LawfulEq Bool where
  eq_is_reflexive = bool_equality_lemmas.reflexive
  eq_is_symmetric = bool_equality_lemmas.symmetric
  eq_is_transitive = bool_equality_lemmas.transitive
  
data ABC = A | B | C

Canonical ABC where
  canonical A = A
  canonical B = A
  canonical C = C
  canonical_is_idempotent A = Refl
  canonical_is_idempotent B = Refl
  canonical_is_idempotent C = Refl

Eq ABC where
  (==) x y with ((canonical x, canonical y))
     | (A, A) = True
     | (C, C) = True  -- have to list matching values individually ?
     | (_, _) = False
