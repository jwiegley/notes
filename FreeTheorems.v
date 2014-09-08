Require Export Coq.Init.Datatypes.
Require Export Coq.Program.Basics.
Require Export Coq.Unicode.Utf8.
Require Export FunctionalExtensionality.

Open Scope list_scope.
Open Scope program_scope.

Theorem filter_free_theorem :
  ∀ (filter : ∀ {X}, (X → bool) → list X → list X),

  ∀ A A' (a : A → A') (a' : list A → list A') (p' : A' → bool),
    a' ∘ @filter A (p' ∘ a) = @filter A' p' ∘ a'.
Proof.
  intros. unfold compose.
  extensionality x.
  induction x; simpl.
Admitted.

Theorem identity_free_theorem :
  ∀ (identity : ∀ {X}, X → X), ∀ A (x : A), identity x = x.
Proof.
  intros.
Admitted.

Reserved Notation "a ⊕ b" (at level 60).

Class Monoid := {
    carrier : Set;
    mempty  : carrier;
    mappend : carrier → carrier → carrier where "a ⊕ b" := (mappend a b);

    left_id : ∀ x, mempty ⊕ x = x;
    right_id : ∀ x, x ⊕ mempty = x;
    assoc : ∀ x y z, (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)
}.

Program Instance List {A : Set} : Monoid := {
    carrier := list A;
    mempty := nil;
    mappend := @app A
}.
Obligation 1. auto. Qed.
Obligation 2.
  intros. induction x; simpl. auto.
  rewrite IHx. reflexivity.
Qed.
Obligation 3.
  intros. induction x; simpl. auto.
  rewrite IHx. reflexivity.
Qed.

Program Instance Sum : Monoid := {
    carrier := nat;
    mempty := 0;
    mappend := plus
}.
Obligation 1. auto. Qed.
Obligation 2. auto. Qed.
Obligation 3.
  intros.
  induction x; simpl. reflexivity.
  f_equal. apply IHx.
Qed.

Class Isomorphism X Y :=
{ to   : X -> Y
; from : Y -> X

; iso_to   : from ∘ to = id
; iso_from : to ∘ from = id
}.

Infix "≅" := Isomorphism (at level 100).

Program Instance Adjointness (A : Type) : (list A → nat) ≅ (A → nat) := {
    to   := fun (f : list A → nat) => fun (x : A)      => f (x :: nil);
    from := fun (f : A → nat)      => fun (x : list A) => length x
}.
Obligation 1.
  intros. unfold compose.
  extensionality f.
  extensionality xs.
  unfold id.
Admitted.
Obligation 2.
  intros. unfold compose.
  extensionality f.
  extensionality x.
  unfold id. simpl.
Admitted.