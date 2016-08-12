Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Program.Equality.

Lemma foo : forall x y, existT id nat x = existT id nat y -> x = y.
Proof.
  intros.
  apply eq_sigT_eq_dep in H.
  dependent destruction H.
  reflexivity.
Qed.

Print Assumptions foo.