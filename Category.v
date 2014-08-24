Lemma surjectivity_is_epic `(f : X → Y) : Surjective f ↔ Epic f.
Proof. unfold Epic, Surjective. split; intros.
- simpl in H0. reduce. unfold func_eqv in H0.
  specialize (H x). destruct H.
  specialize (H0 x0). crush.
- reduce in H.
  specialize H with (Z := Prop).
  specialize H with (g1 := fun y0 => ∃ x0, f x0 = y0).
  specialize H with (g2 := fun y  => True).
  simpl in *. unfold func_eqv in *.
  eapply propositional_extensionality_rev in H.
    destruct H. exists x. crush.
  intros. apply propositional_extensionality.
  exists x. reflexivity.
Qed.
