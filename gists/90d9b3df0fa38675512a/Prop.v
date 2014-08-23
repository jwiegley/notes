Lemma both_ends : forall X (l : list X),
  l = rev l -> nil = l \/ exists x, exists m, x :: snoc m x = l /\ m = rev m.
Proof.
  intros.
  destruct l eqn:Heqe.
    left. reflexivity.
  subst.
  right.
  exists x.
  exists l0.
Admitted.

Lemma app_length' : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1.
  induction l1; intros; simpl; auto.
Qed.

Function rev_pal {X} (l : list X) (H: l = rev l) {measure length l} : pal X l :=
  match both_ends X l H with
  | or_introl P => eq_rect _ _ (pal_nil X) _ P
  | or_intror Q => match Q with
    | ex_intro x p => match p with
      | ex_intro m H => match H with
        | conj L r => eq_rect _ _ (pal_xs X x m (@rev_pal X m r)) _ L
        end
      end
    end
  end.
Proof.
  intros.
  rewrite <- L.
  simpl.
  rewrite snoc_append.
  unfold lt.
  assert (forall Y (s o : list Y), S (length s) <= S (length (s ++ o))).
    intros. rewrite app_length'. apply Le.le_n_S. apply Plus.le_plus_l.
  apply H1.
Qed.
