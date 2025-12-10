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

Notation "'∃'" := (existT _ _).

Inductive Side `(x : X) `(f : X -> A + B) : Type -> Type :=
  | Left  a : f x = inl a -> Side x f A
  | Right b : f x = inr b -> Side x f B.

Definition T (b : bool) : Prop :=
  match b with
  | true  => True
  | false => False
  end.
    
Definition step `(h : X → bool) (x : X) : T (h x) + T (negb (h x)) :=
  match h x as b return T b + T (negb b) with
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
  match f (projT1 s) with
  | inl a => a
  | inr _ => !
  end.
Next Obligation.
  simpl in *.
  unfold is₁, T, compose, join, const in X0.
  destruct (f s) eqn:Heqe.
  - inversion Heq_anonymous.
  - contradiction.
Qed.

Arguments split₁ {X A B}%type_scope f%function_scope _.

Program Definition split₂ `(f : X → A + B) (s : Σ (T ∘ negb ∘ is₁ ∘ f)) : B :=
  match f (projT1 s) with
  | inl _ => !
  | inr b => b
  end.
Next Obligation.
  simpl in *.
  unfold is₁, T, compose, join, const in X0.
  destruct (f s) eqn:Heqe.
  - contradiction.
  - inversion Heq_anonymous.
Qed.

Arguments split₂ {X A B}%type_scope f%function_scope _.

Definition split `(f : X → A + B) :
  ((Σ (T ∘ is₁ ∘ f) → A) * (Σ (T ∘ negb ∘ is₁ ∘ f) → B))%type :=
  (split₁ f, split₂ f).

(** TODO: prove that merge and split form an isomorphism *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.JMeq.

Theorem JMeq_funext
   A (P : A -> Type) (Q : A -> Type)
   (f : forall a, P a)(g : forall a, Q a)
   (h : forall a, JMeq (f a) (g a)) : JMeq f g.
Proof.
  assert (pq_eq : P = Q).
    apply functional_extensionality.
    exact (fun a => match (h a) with JMeq_refl => eq_refl end).
  induction pq_eq.
  assert (fg_eq : f = g).
    apply functional_extensionality_dep.
    exact (fun a => JMeq_rect (fun ga => f a = ga) eq_refl (h a)).
  induction fg_eq.    
  exact JMeq_refl.
Qed.

Lemma JMeq_pair A (a x : A) B (b y : B) :
  a ~= x -> b ~= y -> (a, b) ~= (x, y).
Proof.
  intros.
  now rewrite H, H0.
Qed.

Lemma merge_impl
      `(h : X → bool)
      `(f : Σ (T ∘ h) → A)
      `(g : Σ (T ∘ negb ∘ h) → B) :
  is₁ ∘ merge f g = h.
Proof.
  extensionality x.
  unfold compose, is₁, merge, map_sum, compose, inj₁, inj₂, join.
  unfold step.
  destruct (if h x as b return (T b + T (negb b)) then inj₁ I else inj₂ I) eqn:Heqe.
  + unfold const.
    destruct (h x); auto.
    unfold inj₂ in Heqe.
    inversion Heqe.
  + unfold const.
    destruct (h x); auto.
Qed.

Import EqNotations.

Lemma merge_split `(f : X → A + B) : merge (split₁ f) (split₂ f) = f.
Proof.
  extensionality x.
  unfold merge, split₁, split₂, is₁, map_sum, T, step, compose, join, inj₁, inj₂.
Admitted.

Lemma split₁_merge
      X (h : X → bool)
      A (f : Σ (T ∘ h) → A)
      B (g : Σ (T ∘ negb ∘ h) → B) :
  split₁ (merge f g) ~= f.
Proof.
  pose proof (merge_impl f g).
Admitted.

Lemma split_merge
      X (h : X → bool)
      A (f : Σ (T ∘ h) → A)
      B (g : Σ (T ∘ negb ∘ h) → B) :
  split (merge f g) ~= (f, g).
Proof.
Abort.
