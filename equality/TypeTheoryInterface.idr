%default total

data BasicTypeTheory = Types

interface TypeTheory (theory : Type) (type : Type) | theory where
  void_type : theory -> type
  boolean_type : theory -> type
  nat_type : theory -> type
  sum_type : theory -> type -> type -> type
  fun_type : theory -> type -> type -> type
  
TypeTheory BasicTypeTheory Type where
  void_type Types = Void
  boolean_type Types = Bool
  nat_type Types = Nat
  sum_type Types = Either
  fun_type Types t1 t2 = t1 -> t2
  

example : Type
example = void_type Types = Void
