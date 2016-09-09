Require Export
  Coq.Sets.Ensembles
  Fiat.ADT
  Hask.Control.Monad
  FunctionalExtensionality.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Local Transparent Bind.

Ltac breakdown :=
  try unfold id, comp in *;
  repeat match goal with
  | [ H : ex ?X |- _ ] => destruct H
  | [ |- (fun _ => _) = (fun _ => _) ] =>
      extensionality x; simpl;
      extensionality z; apply prop_ext; split; intros
  | [ |- (exists _, _) = (exists _, _) ] => apply prop_ext
  | [ H : (_ <- _; _)%comp ?Z |- _ ] => destruct H
  | [ H : (_ <- _; _ <- _; _)%comp ?Z |- _ ] => destruct H
  | [ H : (_ <- (_ <- _; _); _)%comp ?Z |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => inversion H; clear H
  | [ |- _ /\ _ ] => split; intros
  | [ H : In _ _ _ |- _ ] => inversion H; clear H
  | [ H : _ = _ |- _ ] => subst
  | [ H : In _ ?X ?Y |- ?X ?Y ] => apply H
  | [ |- _%comp ?Z ] => unfold Bind
  end;
  try eauto;
  try constructor;
  repeat eexists;
  try (eapply (functional_extensionality _); intros);
  try assumption;
  try (apply prop_ext; split; intros; breakdown).

Ltac comp_solver :=
  intros; simpl;
  try solve [
    breakdown;
    try match goal with [ H : _%comp ?Z |- _ ] => destruct H end;
    breakdown
  ].
