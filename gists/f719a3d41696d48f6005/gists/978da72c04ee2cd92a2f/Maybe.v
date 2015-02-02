Ltac simple_solver :=
  try ext_eq;
  compute;
  repeat (match goal with
    | [ |- context[match ?X with _ => _ end] ] =>
      match X with
      | match _ with _ => _ end => fail
      | _ => destruct X; auto
      end
    end
    );
  auto.
