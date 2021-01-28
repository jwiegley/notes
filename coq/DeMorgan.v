Lemma not_or_ (φ ψ : Prop) : ~ (φ \/ ψ) <-> ~ φ /\ ~ ψ.
Proof.
  split; intros.
  - split; intro.
    + apply H.
      now left.
    + apply H.
      now right.
  - destruct H.
    intro.
    destruct H1.
    + contradiction.
    + contradiction.
Qed.

Lemma not_and_ (φ ψ : Prop) : ~ (φ /\ ψ) <-> ~ φ \/ ~ ψ.
Proof.
  split; intros.
  - apply NNPP.
    intro.
    apply H.
    split.
    + apply not_or_ in H0.
      firstorder.
    + apply not_or_ in H0.
      firstorder.
  - destruct H.
    intro.
    + now apply H.
    + intro.
      now apply H.
Qed.

