Axiom omega : Type.

Definition set := omega -> Prop.

Axiom ext : forall x y : set, (forall o, x o <-> y o) -> x = y.

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).
Definition union (a b : set) := fun x => a x \/ b x.
Definition is_included (a b : set) := forall x, a x -> b x.

Lemma union_comm : forall x y : set, union x y = union y x.
Proof.
  intros x y. apply ext.
  intro o. unfold union.
  split.
    intros. destruct H.
      right. apply H.
      left. apply H.
    intros. destruct H.
      right. apply H.
      left. apply H.
Qed.

Print False.