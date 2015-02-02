Axiom predicate_extensionality : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x <-> Q x) -> P = Q.

Lemma func_ext : forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.
Proof.
  intros.
  apply (@predicate_extensionality A).

Lemma eta : forall A B (f : A -> B),
  (fun x => f x) = f.
Proof. intros. apply func_ext. auto. Qed.

Lemma prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.
Proof.
  intros.
  pose (@predicate_extensionality Prop (fun _ => P) (fun _ => Q)).
  simpl in e. apply e.

Lemma proof_irrelevance : forall (P : Prop) (u v : P), u = v.

Lemma prop_degeneracy : forall (P : Prop),
   P = True \/ P = False.
Proof.
  intros. destruct (classic P).
  left. apply prop_ext. tauto.
  right. apply prop_ext. tauto.
Qed.
