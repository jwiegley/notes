Require Recdef.

Fixpoint map {a b : Set} (f : a -> b) (xs : list a) : list b :=
  match xs with
    | nil => nil
    | cons x x0 => cons (f x) (map f x0)
  end.

Theorem map_preserves_length : forall {a b : Set} (f : a -> b) (xs : list a),
  length xs = length (map f xs).
Proof.
  intros. induction xs as [| y ys].
    reflexivity.
  simpl. rewrite IHys. reflexivity.
Defined.

Function h (f : nat -> nat) (xs : list nat) {measure length xs} :=
  match map f xs with
    | nil => 0
    | cons y ys => y + h f ys
  end.
Proof.
  intros.
  rewrite (map_preserves_length f xs).
  rewrite teq.
  auto.
Qed.