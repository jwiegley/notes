Require Export Coq.Sets.Ensembles.

Lemma Subtract_Add_equiv {X} (r : Ensemble X) x :
  ~ In _ r x -> Subtract _ (Add _ r x) x = r.
Proof.
  intros.
  rewrite (@Extensionality_Ensembles _ (Subtract _ (Add _ r x) x) r).
    reflexivity.
  split; unfold Included; intros.
    inversion H0; clear H0.
    inversion H1; clear H1; subst.
      assumption.
    contradiction.
  split.
    constructor.
    assumption.
  unfold not; intros.
  inversion H1; clear H1; subst.
  contradiction.
Qed.

Lemma Add_Subtract_equiv {X} (r : Ensemble X) x :
  forall (eqdec : forall a b : X, {a = b} + {a <> b}),
    In _ r x -> Add _ (Subtract _ r x) x = r.
Proof.
  intros.
  rewrite (@Extensionality_Ensembles _ (Add _ (Subtract _ r x) x) r).
    reflexivity.
  split; unfold Included; intros.
    inversion H0; clear H0; subst.
      inversion H1.
      assumption.
    inversion H1; clear H1; subst.
    assumption.
  unfold In, Add, Subtract, Setminus.
  destruct (eqdec x x0).
    subst.
    right.
    constructor.
  left.
  constructor.
    assumption.
  unfold not; intros.
  inversion H1; clear H1; subst.
  contradiction n.
  reflexivity.
Qed.
