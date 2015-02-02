Require Import Bool NPeano ZArith.

Definition is_true n := n = true.
Coercion is_true : bool >-> Sortclass.

Functional Scheme even_ind := Induction for even Sort Prop.
Lemma ltn_even : forall n m, even n /\ even m -> n < m -> n + 1 < m.
Proof.
  intro n; apply even_ind.
  intros n0 ? m H.
  destruct m as [|[|m]]; simpl in *; solve [omega|discriminate H].
  intros ? ? ? ? ? H; discriminate H.
  intros ? ? ? ? ? IH m H H0; destruct m as [|[|m]];[omega|simpl in H0; omega|].
  simpl in H; apply IH in H;omega.
Qed.