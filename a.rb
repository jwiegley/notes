Lemma termD_rect (P : ∀ dom cod (f' : objs dom ~> objs cod) (f : Term), Type) :
  (∀ dom, P dom dom id Identity)
    -> (∀ a dom cod f', arrs a = Some (dom; (cod; f')) -> P dom cod f' (Morph a))
    -> (∀ f mid cod f', termD mid cod f = Some f'
          -> P mid cod f' f
          -> ∀ g dom g', termD dom mid g = Some g'
          -> P dom mid g' g -> P dom cod (f' ∘ g') (Compose f g))
    -> ∀ f dom cod f', termD dom cod f = Some f' -> P dom cod f' f.
Proof.
  unfold termD.
  induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate]; subst; auto.
    inversion H0; subst.
    now apply X.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct (Pos.eq_dec x dom); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    inversion H0; subst.
    now apply X0.
  - destruct (termD_work dom f2) eqn:?; [|discriminate].
    destruct s.
    destruct (termD_work x f1) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst; simpl in *.
    specialize (IHf1 x cod h0).
    specialize (IHf2 dom x h).
    rewrite Heqo0, Pos_eq_dec_refl in IHf1.
    rewrite Heqo, Pos_eq_dec_refl in IHf2.
    specialize (IHf1 eq_refl).
    specialize (IHf2 eq_refl).
    specialize (X1 f1 x cod h0).
    rewrite Heqo0, Pos_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf1 f2 dom h).
    rewrite Heqo, Pos_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf2).
    inversion H0; subst.
    apply X1.
Defined.

Lemma termD_ValidTerm {dom cod f f'} :
  termD dom cod f = Some f' -> ValidTerm dom cod f.
Proof.
  intros.
  pattern f, dom, cod, f', H0.
  refine (termD_rect (fun dom cod f' f => ValidTerm dom cod f) _ _ _ f _ _ _ _);
  intros; try econstructor; eauto.
Defined.
