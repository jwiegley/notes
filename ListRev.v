Require Import Coq.Lists.List.
Import ListNotations.

Lemma app_inv :
  forall A (x y : A) xs ys, xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y.
Proof.
  induction xs; simpl; intros.
    destruct ys; simpl in *.
      inversion H.
      auto.
    inversion H.
    destruct ys; discriminate.
  split.
    destruct ys; simpl in *.
      inversion H.
      destruct xs; discriminate.
    inversion H.
    apply IHxs in H2.
    inversion H2.
    subst.
    reflexivity.
  destruct ys; simpl in *.
    inversion H.
    destruct xs; discriminate.
  inversion H.
  apply IHxs in H2.
  inversion H2.
  subst.
  reflexivity.
Qed.

Goal forall A (xs ys : list A), rev xs = rev ys -> xs = ys.
Proof.
  induction xs; intros.
    destruct ys; simpl; auto.
    simpl in H.
    destruct (rev ys); discriminate.
  destruct ys; simpl in H.
    destruct (rev xs); discriminate.
  apply app_inj_tail in H.
  inversion H.
  f_equal; auto.
Qed.
