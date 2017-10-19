Inductive Foo (A : Type) := Mk_Foo : list (Foo A) -> Foo A.

Function foo (xs : Foo nat) : bool :=
  match xs with | Mk_Foo xs' =>
    List.any (fun n : Foo nat => foo n) xs'
  end.
