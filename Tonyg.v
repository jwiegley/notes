Require Import List.

Import ListNotations.

Lemma help : forall a (x : a) xs, x :: xs = [x] ++ xs.
Proof.
  intros.
  generalize dependent x.
  induction xs; auto.
Qed.

Lemma tonyg : forall a (xs1 xs2 ys : list a),
  xs1 ++ ys = xs2 ++ ys -> xs1 = xs2.
Proof.
  intros.
  generalize dependent xs1.
  generalize dependent xs2.
  induction ys; simpl; intros.
    rewrite app_nil_r in H.
    rewrite app_nil_r in H.
    assumption.
  simpl in H.
  rewrite help in H.
  rewrite app_assoc in H.
  rewrite app_assoc in H.
  apply IHys in H.
  apply app_inj_tail in H.
  inversion H.
  assumption.
Qed.