Inductive Vec (A : Type) : nat -> Type :=
  | Vnil    : Vec A 0
  | Vcons n : A -> Vec A n -> Vec A n.+1.
