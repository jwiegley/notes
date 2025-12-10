Require Import Coq.Logic.ProofIrrelevance.

Definition antal {A : Prop} : inhabited A -> A.
Proof.
  intros.
  destruct H.