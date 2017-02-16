Fixpoint plus' (x y : nat) :=
  match x with
  | O => y
  | S x => S (plus' x y)
  end.

Lemma plus'_unit_right : forall y, plus' y 0 = y.
Proof.
  intros y.
  induction y.
    simpl.
    reflexivity.
  simpl.
  rewrite IHy.
  reflexivity.
Qed.

Lemma plus'_S1 : forall y, S y = plus' y 1.
Proof.
  intros y.
  induction y.
    simpl.
    reflexivity.
  simpl.
  rewrite <- IHy.
  reflexivity.
Qed.

Lemma plus'_distr : forall n m : nat, S (plus' n m) = plus' n (S m).
Proof.
  intros n m.
  induction n.
    simpl.
    reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem plus'_commutative : forall x y, plus' x y = plus' y x.
Proof.
  intros x y.
  generalize dependent y.
  induction x.
    simpl.
    intros y.
    rewrite plus'_unit_right.
    reflexivity.
  intros y.
  simpl.
  rewrite IHx.
  clear IHx.
  apply plus'_distr.
Qed.