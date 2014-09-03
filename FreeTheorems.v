Require Export Coq.Init.Datatypes.
Require Export Coq.Program.Basics.
Require Export Coq.Unicode.Utf8.
Require Export FunctionalExtensionality.

Open Scope list_scope.
Open Scope program_scope.

Theorem filter_free_theorem :
  ∀ (filter : ∀ {x}, (x → bool) → list x → list x),

  ∀ A A' (a : A → A') (a' : list A → list A') (p' : A' → bool),
    a' ∘ filter (p' ∘ a) = filter p' ∘ a'.
Proof.
  intros. unfold compose.
  extensionality x.
  induction x; simpl.
    repeat rewrite H.
Admitted.
