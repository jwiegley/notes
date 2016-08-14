CoInductive stream (A : Type) := scons : A -> stream A -> stream A.

CoFixpoint series (n : nat) : stream nat := scons n (series (S n)).

Fixpoint zip {A B} (xs : stream A) (ys : list B) : list (A * B) :=
  match xs with
  | scons x xs =>
    match ys with
    | nil => nil
    | cons y ys => (x, y) :: zip xs ys
    end
  end.

Require Import Coq.Lists.List.

Lemma In_zip_series : forall A (x : A) xs n i, n <= i
  -> List.In (S i, x) (zip (series n) xs)
  -> exists y, In (i, y) (zip (series n) xs).
Proof.
  Require Import Omega.
  intros.
  generalize dependent n.
  induction xs; intros.
    inversion H0.
  simpl in H0.
  destruct H0.
    inv H0.
    abstract omega.
  simpl.
  specialize (IHxs (S n)).
  destruct (Peano_dec.eq_nat_dec n i).
    exists a.
    subst.
    left; reflexivity.
  assert (not_really_le : forall n i, n <= i -> n <> i -> S n <= i)
    by (intros; abstract omega).
  specialize (IHxs (not_really_le _ _ H n0) H0).
  destruct IHxs.
  exists x0.
  right.
  exact H1.
Qed.

Lemma In_ascending : forall A (x : A) xs n m,
  n < m -> ~ In (n, x) (zip (series m) xs).
Proof.
  unfold not.
  induction xs; simpl; intros.
    contradiction.
  destruct H0.
    inv H0.
    firstorder.
  apply IHxs with (n:=n) (m:=S m).
    omega.
  assumption.
Qed.

Lemma In_zip_at_index : forall i n A (x y : A) xs,
  In (i, x) (zip (series n) xs) -> In (i, y) (zip (series n) xs) -> x = y.
Proof.
  intros.
  generalize dependent n.
  induction xs; simpl; intros.
    contradiction.
  destruct H, H0.
  + inv H; inv H0; reflexivity.
  + inv H.
    apply In_ascending in H0; [contradiction|omega].
  + inv H0.
    apply In_ascending in H; [contradiction|omega].
  + apply (IHxs (S n)); trivial.
Qed.
