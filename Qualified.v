Require Import List.
Set Implicit Arguments.

Lemma id_x : forall A (x:A), id x = x. auto. Qed.

Lemma wrap : forall A B (f:A -> B), f = fun a:A => f a. auto. Qed.

Lemma map_id_id : forall A (x:list A), map id x = id x.
  intros.
  rewrite wrap with A A id.
  rewrite id_x.
  induction x; auto; simpl. rewrite IHx. rewrite id_x. reflexivity.
Qed.