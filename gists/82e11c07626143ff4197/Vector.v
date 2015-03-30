Definition Vec : nat -> Type :=
  fix vec n := match n return Type with
               | O   => unit
               | S n => prod A (vec n)
               end.
