Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Fixpoint denote (xs : list ascii) : string :=
  match xs with
  | nil => EmptyString
  | cons x xs => String x (denote xs)
  end.

Fixpoint reify (xs : string) : list ascii :=
  match xs with
  | EmptyString => nil
  | String x xs => cons x (reify xs)
  end.

Lemma denote_reify : forall x, denote (reify x) = x.
Admitted.

Lemma denote_sound :
  forall (P : string -> Prop) x,
  P (denote (reify x)) <-> P x.
Proof.
  intros.
  induction x; simpl; split; intros; auto.
    rewrite denote_reify in H; auto.
  rewrite denote_reify; auto.
Qed.
