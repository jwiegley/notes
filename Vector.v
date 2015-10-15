Definition transpose {m n : nat} a : Vec (Vec a n) m -> Vec (Vec a m) n.
Proof.
  move=> v.
  elim: m => /= [|m IHm] in v *.
    by elim: n.
  inv v.
  elim: n => //= [n IHn] in IHm X X0 *.
  split.
    split.
      by case: X.
    by case: IHm.
  apply: IHn.
    move=> Y.
      by case: IHm.
    by case: X.
  exact: vmap snd X0.
Defined.
