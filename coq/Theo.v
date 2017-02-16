Require Import Coq.Lists.List.
Import ListNotations.

Require Import Program.Equality.

Import EqNotations.

Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.

Goal forall a (xs : list a) x ys P (H1 : Forall P ((xs ++ [x]) ++ ys))
            (H2 : Forall P (xs ++ (x::ys))), H1 ~= H2.
Proof.
  intros.
  revert H1.
  rewrite <- app_assoc.
  simpl.
  intros.
  assert (H1 = H2).
    apply prop_extensionality.
  apply Forall_forall in H1.
  apply JMeq_refl.
Qed.

Goal forall a (xs : list a) x ys P (H1 : Forall P (xs ++ [x] ++ ys)) (H2 :
Forall P (xs ++ (x::ys))), H1 = H2.
