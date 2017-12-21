Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.

Fixpoint nth_le {A: Type} (l: list A) (n: nat) (h: n < length l): A.
Proof.
  destruct n.
    destruct l.
      apply PeanoNat.Nat.nlt_0_r in h.
      contradiction.
    exact a.
  destruct l.
    apply PeanoNat.Nat.nlt_0_r in h.
    contradiction.
  simpl in h.
  apply Lt.lt_S_n in h.
  exact (nth_le _ l n h).
Defined.

Lemma nth_le_induct {A} l n (X : A) h1 h2:
  nth_le (X :: l) (S n) h1 = nth_le l n h2.
Proof.
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.
