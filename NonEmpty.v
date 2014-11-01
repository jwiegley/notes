Inductive NonEmpty (a : Type) := NE s of @size a s > 0.

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a := let: NE x _ := ne in x.

Coercion NE_to_list : NonEmpty >-> list.

Definition ne_ind : forall (A : Type) (P : NonEmpty A -> Type),
  (forall (a : A), P (@NE A [:: a] (ltn0Sn 0))) ->
  (forall (a : A) (l : NonEmpty A),
     P l -> P (@NE A (a :: l) (ltn0Sn (size l)))) ->
  forall l : NonEmpty A, P l.
Proof.
  move=> A P H1 H2.
  case. elim=> [//|x xs IHx] H.
  case: xs => [|y ys] in IHx H *.
    have irr: ltn0Sn 0 = H by exact: proof_irrelevance.
    rewrite -irr.
    exact: H1.
  have irr: ltn0Sn (size (y :: ys)) = H by exact: proof_irrelevance.
  rewrite -irr.
  eapply (H2 x (@NE _ (y :: ys) _)).
  apply IHx.

  Grab Existential Variables.
  by [].
Defined.

Definition NE_length {a} : NonEmpty a -> nat := size.

Lemma NE_length_spec {a} : forall ne : NonEmpty a, NE_length ne > 0.
Proof. by case. Qed.

Definition NE_head {a}: NonEmpty a -> a.
Proof. elim/ne_ind=> //. Defined.

Definition NE_last {a} : NonEmpty a -> a.
Proof.
  elim/ne_ind=> [x|x xs IHxs].
    exact: x.
  exact: IHxs.
Defined.
