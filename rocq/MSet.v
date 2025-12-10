Require Import Coq.MSets.MSets.

Inductive MyType := Foo | Bar.

Definition compare_My_Type (x y : MyType) :=
  match x, y with
  | Foo, Foo => Eq
  | Foo, Bar => Lt
  | Bar, Foo => Gt
  | Bar, Bar => Eq
  end.

Module MyType_as_OT <: OrderedType.

  Definition t := MyType.
  Definition compare := compare_My_Type.

  Definition eq := @eq MyType.
  Definition lt := fun x y => compare_My_Type x y = Lt.

  Instance eq_equiv : Equivalence eq := eq_equivalence.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - intro x. destruct x.
        unfold complement. intros.
        inversion H.
      unfold complement. intros.
      inversion H.
    - unfold Transitive; intros.
      unfold lt in *.
      unfold compare_My_Type in *.
      destruct x, y, z; auto.
      discriminate.
      discriminate.
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof. intros x x' Hx y y' Hy; rewrite Hx, Hy; split; auto. Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros.
    unfold CompSpec.
    destruct x, y; try constructor; reflexivity.
  Qed.

  Definition eq_dec : forall x y, { eq x y } + { ~eq x y }.
  Proof.
    intros.
    destruct x, y; simpl.
    left. reflexivity.
    right. unfold not. intros. discriminate.
    right. unfold not. intros. discriminate.
    left. reflexivity.
  Qed.

End MyType_as_OT.

Module S := MSetAVL.Make(MyType_as_OT).
Module Import N := WPropertiesOn S.E S.

Lemma elements_spec3 : forall s x, In x (S.elements s) <-> S.In x s.
Proof.
  split; intros.
  - apply S.elements_spec1.
    apply InA_alt.
    exists x.
    split. reflexivity.
    assumption.
  - apply S.elements_spec1 in H.
    apply InA_alt in H.
    destruct H.
    inversion H.
    rewrite H0.
    assumption.
Qed.

Lemma remove_over_not : forall x e s, ~ S.In x s -> ~ S.In x (S.remove e s).
Proof.
  intros. unfold not in *. intros.
  apply H. apply S.remove_spec in H0.
  inversion H0. assumption.
Qed.

Definition mySet : Type := S.t.  (* the type of a set of MyTypes *)
