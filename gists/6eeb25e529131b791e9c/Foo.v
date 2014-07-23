Lemma plist_in_out : forall ls, plistOut (plistIn ls) = ls.
Proof.
  induction ls as [|x t].
    auto.
    assert (x :: plistOut (plistIn t) = plistOut (plistIn (x :: t))).
      admit.
    rewrite <- H.
    rewrite IHt.
    reflexivity.
Qed.
