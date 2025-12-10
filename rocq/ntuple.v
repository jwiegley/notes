Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SetNthTuple.

  Variables (n : nat) (T : Type).
  Implicit Types (i : 'I_n) (t : n.-tuple T) (x : T).

  Lemma set_nth_tupleP t i x :
    size (set_nth x t i x) == n.
  Proof. by rewrite size_set_nth size_tuple maxnE subnKC. Qed.

  Canonical set_nth_tuple t i x := Tuple (set_nth_tupleP t i x).

  Definition tset_nth t i x := [tuple of set_nth x t i x].

  Lemma tnth_tset_nth t i y : tnth (tset_nth t i y) =1 [eta tnth t with i |-> y].
  Proof. by move=> idx; rewrite /= -val_eqE !(tnth_nth y) nth_set_nth. Qed.

End SetNthTuple.

Lemma vnth_replace_neq (T : eqType) n z
      (t : n.-tuple T)
      (k j : 'I_n) :
  j != k ->
  tnth (tset_nth t k z) j = tnth t j.
Proof. by rewrite tnth_tset_nth=> /=/negbTE->. Qed.

