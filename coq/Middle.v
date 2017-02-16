Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.


Theorem classic_excluded_middle : classic -> excluded_middle.
Proof.
  unfold classic. unfold excluded_middle.
  intros.
  unfold not in H. unfold not.
  left. apply H.
  intro.
  apply H0 in H. apply H. (* So what does apply do here? *)