Ltac submatch X :=
  match X with
  | match ?Y with _ => _ end => submatch Y
  | _ => destruct X; auto
  end.

Ltac simple_solver :=
  intros;
  try ext_eq;
  compute;
  repeat (
    match goal with
    | [ |- context f [match ?X with _ => _ end] ] =>
      submatch X
    end);
  auto.
