Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia.

Set Implicit Arguments.
Set Asymmetric Patterns.
Generalizable All Variables.

Definition join `(f : A → C) `(g : B → C) : A + B → C :=
  fun x => match x with
           | inl x => f x
           | inr x => g x
           end.

Notation "[ f , g ]" := (join f g) (at level 100).

Definition inj₁ {A B : Type} : A -> A + B := inl.
Definition inj₂ {A B : Type} : B -> A + B := inr.

Definition map_sum `(f : A → C) `(g : B → D) : A + B → C + D :=
  [ inj₁ ∘ f , inj₂ ∘ g ].

Infix "⊕" := map_sum (at level 80, right associativity).

Notation "'Σ'" := sigT.

Definition T (b : bool) : Prop :=
  match b with
  | true  => True
  | false => False
  end.
    
Program Definition step `(h : X → bool) (x : X) : T (h x) + T (negb (h x)) :=
  match h x with
  | true  => inj₁ I
  | false => inj₂ I
  end.

(** Thanks to Arjan Rouvoet for suggesting step. *)

Definition merge
           `(h : X → bool)
           `(f : Σ (T ∘ h) → A)
           `(g : Σ (T ∘ negb ∘ h) → B)
           (x : X) : A + B :=
  ((f ∘ existT _ x) ⊕ (g ∘ existT _ x)) (step h x).

Definition is₁ {A B : Type} : A + B → bool :=
  [ const true , const false ].

Program Definition split₁ `(f : X → A + B) (s : Σ (T ∘ is₁ ∘ f)) : A :=
  match s with
  | existT x q =>
    match f x with
    | inl a => a
    | inr _ => !
    end
  end.
Next Obligation.
  destruct (f s) eqn:Heqe.
  - inversion Heq_anonymous.
  - unfold compose in q.
    rewrite Heqe in q.
    simpl in q.
    contradiction.
Qed.

Arguments split₁ {X A B}%type_scope f%function_scope _.

Program Definition split₂ `(f : X → A + B) (s : Σ (T ∘ negb ∘ is₁ ∘ f)) : B :=
  match s with
  | existT x q =>
    match f x with
    | inl _ => !
    | inr b => b
    end
  end.
Next Obligation.
  destruct (f s) eqn:Heqe.
  - unfold compose in q.
    rewrite Heqe in q.
    simpl in q.
    contradiction.
  - inversion Heq_anonymous.
Qed.

Arguments split₂ {X A B}%type_scope f%function_scope _.

Definition split `(f : X → A + B) :
  Σ (λ h, (Σ (T ∘ h) → A) * (Σ (T ∘ negb ∘ h) → B))%type :=
  existT _ (is₁ ∘ f) (split₁ f, split₂ f).

(** TODO: prove that merge and split form an isomorphism *)
