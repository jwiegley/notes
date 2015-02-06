Lemma StronglySorted_skip : forall a R (y : a) a0 ys,
  StronglySorted R [:: y, a0 & ys] -> StronglySorted R (y :: ys).
Proof.
  move=> a R y a0 ys H.
  elim: ys => [|z zs IHzs] in H *.
    by constructor; constructor.
  constructor.
    by constructor; inv H; inv H2; inv H1.
  by inv H; inv H3.
Qed.

Lemma StronglySorted_cat
  {A : Type} {x y : A} {xs ys : seq A} {R : A -> A -> Prop}
  `{Transitive _ R} :
  StronglySorted R (x :: xs) ->
  StronglySorted R (y :: ys)
    -> R (last x xs) y
    -> StronglySorted R (x :: xs ++ y :: ys).
Proof.
  move=> rel Hsort1 Hsort2.
  constructor.
    induction xs; simpl in *.
      induction ys; simpl in *.
        constructor.
          by constructor.
        by constructor.
      assumption.
    constructor.
      apply: IHxs.
        inv rel.
        constructor.
          by inv H2.
        by inv H3.
      induction xs; simpl in *.
        inv rel; inv H3.
        by transitivity a.
      assumption.
    induction xs; simpl in *.
      have H1: StronglySorted R [:: x]
        by constructor; constructor.
      have H2: R x y.
        inv rel; inv H4.
        by transitivity a.
      specialize (IHxs H1 H2).
      induction ys; simpl in *.
        by constructor.
      constructor=> //=.
      inv Hsort1; inv H4; inv H5.
      constructor.
        by transitivity y.
      specialize (IHys (SSorted_cons y H6 H8)
                       (StronglySorted_skip IHxs)).
      by inv IHys.
    constructor; inv rel.
      by inv H2; inv H5.
    apply: IHxs0 => /=.
    - constructor.
        exact: StronglySorted_skip.
      constructor.
        by inv H3.
      by inv H3; inv H5.
    - destruct xs. simpl in *.
        inv H2; inv H5.
        by transitivity a0.
      by [].
    - move=> H4 H5.
      destruct xs. simpl in *.
        move: (SSorted_cons x H2 H3) => H6.
        specialize (IHxs (StronglySorted_skip H6) Hsort2).
        by inv IHxs.
      move: (SSorted_cons x H2 H3) => H6.
      specialize (IHxs (StronglySorted_skip H6) Hsort2).
      by inv IHxs.
  induction xs; simpl in *.
    induction ys; simpl in *.
      by constructor.
    constructor=> //.
    inv Hsort1; inv H2; inv H3.
    constructor.
      by transitivity y.
    specialize (IHys (SSorted_cons y H4 H6)).
    by inv IHys.
  constructor; inv rel.
    by inv H3.
  apply: IHxs.
    constructor.
      by inv H2.
    by inv H3.
  inv H2; inv H3.
  induction xs; simpl in *.
    by transitivity a.
  assumption.
Qed.
