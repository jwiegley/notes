Goal forall P, Decidable.decidable P -> ~(P /\ ~P) -> (P \/ ~P).
Proof.
  move=> P Pdec H.
  move: (Decidable.not_and P (~P) Pdec H) => [H1|H2].
    by right.
  left.
  move: (Decidable.not_not P Pdec).
  by move=> /(_ H2).
Qed.

