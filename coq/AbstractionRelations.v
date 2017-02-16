(** This is a sample file to demonstrate the definition and use of an
    “abstraction relation”, as defined in the Fiat literature:

    Fiat uses abstraction relations to enable representation type
    refinement. An abstraction relation [A ≈ B] between two ADTs
    implementing a common signature [ASig] is a binary relation on the
    representation types [A.rep] and [B.rep] that is preserved by the
    operations specified in [ASig]. In other words, the operations of
    the two ADTs take “similar” input states to “similar” output
    states. Since operations in Fiat are implemented as computations,
    the methods of [B] may be computational refinements of [A]. Thus,
    an ADT method [B.m] is a refinement of [A.m] if

      A.m ≃ B.m ≡ ∀ rA rB. rA ≈ rB                       →
                  ∀ i rB′ o. B.m(rB,i) ↝ (rB′,o)         →
                  ∃ rA′. A.m(rA,i) ↝ (rA′,o) ∧ rA′ ≈ rB′

    The quantified variable [i] stands for the method’s other inputs,
    beside the “self” value in the data type itself; and [o] is
    similarly the parts of the output value beside “self.”
 *)

Require Export Coq.Sets.Ensembles.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Relations.Relations.
Require Export Utf8_core.

Require Import Fiat.Common.

Generalizable All Variables.

(** In order to fully describe what an abstraction relation is and does, we
    must first establish some background in terms of how Fiat encodes
    computations, and refinement over computations. *)

(** A [Comp], or abstract computation, is another name for an [Ensemble]: a
    set defined propositionally by its membership ([∀ x, x -> Prop]). *)
Definition Comp := @Ensemble.

(** [Return] is the most basic computation; it represents a singleton set
    containing one inhabitant of the given type [A]. *)
Definition Return (A : Type) : A -> Comp A := Singleton A.

(** [Bind] composes a set with a set-producing function to determine the union
    of the resulting sets.

    For example, for every member of some input set of type [A], the function
    [k] yields a new set of type [B], so that the immediate result is a set of
    sets of type [B], one for every [A] in the input. This aggregate is then
    flattened by union to a single set of type [B]. *)
Definition Bind (A B : Type) (ca : Comp A) (k : A -> Comp B) : Comp B :=
  fun b => exists a : A, In A ca a /\ In B (k a) b.

(** [Pick] chooses inhabitants of some type [A] to form a particular set or
    computation over members of that type. It may be read as "inhabitants of
    [A] for which [P] holds", or using set notation: [{ x : A | P }]. *)
Definition Pick (A : Type) (P : Ensemble A) : Comp A := P.

Delimit Scope comp_scope with comp.
Bind Scope comp_scope with Comp.
Arguments Bind [A%type B%type] ca%comp k _.
Arguments Return [_] _ _.
Arguments Pick [_] _ _.

(** [ret] is a printing synonym for [Return]. *)
Notation ret := Return.

Notation "x >>= y" :=
  (Bind x%comp y%comp) (at level 42, right associativity) : comp_scope.
Notation "x <- y ; z" :=
  (Bind y%comp (fun x => z%comp))
    (at level 81, right associativity,
     format "'[v' x  <-  y ; '/' z ']'") : comp_scope.
Notation "x >> z" :=
  (Bind x%comp (fun _ => z%comp))
    (at level 81, right associativity,
     format "'[v' x >> '/' z ']'") : comp_scope.

Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick A%type (fun x => P)) : comp_scope.

(** [computes_to] provides evidence that a given inhabitant [a] of type [A]
    exists within the set or computation [ca]. This is also given by the
    notation [ca ↝ a], or in set notation [a ∈ ca], or in the parlance of
    Coq's [Ensemble] library: [ca a]. *)
Definition computes_to {A : Type} (ca : Comp A) (a : A) : Prop := ca a.

Notation "c ↝ v" := (computes_to c v) (at level 70).

(** Proof that [Return] of a value results in a set containing that value, or
    "computes to that value". This is tautological, being the definition of
    [Return]. *)
Lemma ReturnComputes `(a : A) :
  ret a ↝ a.
Proof. constructor. Qed.

(** Proof that if [ca] computes to [a], and [f a] computes to [b], then
    binding [ca >>= f] computes to [b].

    Follows trivially from the definition of [Bind]. *)
Lemma BindComputes `(ca : Comp A) `(f : A -> Comp B) (a : A) (b : B) :
  ca ↝ a -> f a ↝ b -> (ca >>= f) ↝ b.
Proof. econstructor; eauto. Qed.

(** Proof that if [P a] is true, then picking [a'] using [P a] computes to
    [a].

    Follows trivially from the definition of [Pick]. *)
Lemma PickComputes `(P : Ensemble A) (a : A) :
  P a -> {a' | P a'} ↝ a.
Proof. intros; eauto. Qed.

(** [Return_inv] tells is that if [ret a] computes to [v], it must be the case
    that [a = v]. Thus we can "invert" a statement about computability to
    derive an equality. *)
Lemma Return_inv {A} (a v : A) :
  ret a ↝ v -> a = v.
Proof. destruct 1; reflexivity. Qed.

(** [Bind_inv] inverts a statement about the computability of a bind statement
    [ca >>= f ↝ v] to yield two pieces of implied information:

    1. That there does exist an element [a':A] where [ca ↝ a'].
    2. That [f a' ↝ v]. *)
Lemma Bind_inv `(ca : Comp A) `(f : A -> Comp B) (v : B) :
  ca >>= f ↝ v -> exists a', ca ↝ a' /\ f a' ↝ v.
Proof. destruct 1; eauto. Qed.

(** [Pick_inv] trivially shows that if we pick some element [a] for which
    [P a] is true, and this computes to [v], then [P v] is also true. *)
Lemma Pick_inv `(P : Ensemble A) (v : A) :
  {a | P a} ↝ v -> P v.
Proof. eauto. Qed.

(** A computation is said to be refined if every value computable from the
    [new] computation can be computed from the [old] computation. Note that
    this does not say that every [old] computable value is also computable by
    [new], so it is a subset of what was computable before the refinement.
    Thus, another way of stating this is [new ⊆ old], since computations are
    modelled as typed sets. *)
Definition refine {A} (old : Comp A) (new : Comp A) :=
  forall v, new ↝ v -> old ↝ v.

(** A [Refinement_Of] some computation [c] is any computation [c'] for which
    it is true that [refine c c'].

    Such a refinement [c'] has the notation [Refinement of c]. *)
Definition Refinement_Of {A} (c : Comp A) := {c' | refine c c'}.

Notation "'Refinement' 'of' c" :=
  {c' | refine c c'}
    (at level 0, no associativity,
     format "'Refinement'  'of' '/' '[v'    c ']' " ) : comp_scope.

(** Two computations are equivalent if each refines the other. This
    establishes a bijection between the two computations. *)
Definition refineEquiv {A} (old : Comp A) (new : Comp A) :=
  refine old new /\ refine new old.

(** We also state computation equivalent directly as bi-implication, over a
    single quantified variable [v]. *)
Definition equiv {A} (c1 c2 : Comp A) := forall v, c1 ↝ v <-> c2 ↝ v.

Infix "~" := equiv (at level 70) : comp_scope.

(** [refineEquiv] and [equiv] are themselves equivalent. They differ only in
    the scope of the universally quantified variables used, that is:

      [(∀ x, P x) ‌∧ (∀ x, Q x) ↔ (∀ x, P x ∧ Q x)]
 *)
Lemma refineEquiv_iff_equiv {A} (x y : Comp A) :
  refineEquiv x y <-> equiv x y.
Proof.
  unfold refineEquiv, refine.
  split; intros.
  destruct H; split; intros; auto.
  split; intros; destruct (H v); auto.
Qed.

Local Ltac t :=
  repeat first [ solve [ unfold computes_to in *; eauto ]
               | progress hnf in *
               | intro
               | split
               | progress split_and ].

Global Instance refine_PreOrder A : PreOrder (@refine A).
t.
Qed.

Global Instance refineEquiv_Equivalence A : Equivalence (@refineEquiv A).
t.
Qed.

Global Instance equiv_Equivalence A : Equivalence (@equiv A).
t.
- specialize (H v).
  destruct H; apply H1, H0.
- specialize (H v).
  destruct H; apply H, H0.
- specialize (H v).
  destruct H; apply H0, H, H1.
- specialize (H v).
  destruct H; apply H2, H0, H1.
Qed.

Global Opaque Return.
Global Opaque Bind.
Global Opaque Pick.
Global Opaque computes_to.

Global Hint Resolve ReturnComputes.
Global Hint Resolve BindComputes.
Global Hint Resolve PickComputes.

Ltac computes_to_inv :=
  repeat match goal with
         | H : {a' | @?P a'} ↝ _ |- _ => apply Pick_inv in H
         | H : Return ?a ↝ _ |- _ => apply Return_inv in H
         | H : Bind (A := ?A) ?ca ?k ↝ _ |- _ =>
           apply Bind_inv in H;
             let a' := fresh "v" in
             let H' := fresh H "'" in
             destruct H as [a' [H H']]
         end.

Ltac computes_to_econstructor :=
  first
    [ unfold refine; intros; eapply @ReturnComputes
    | unfold refine; intros; eapply @BindComputes
    | unfold refine; intros; eapply @PickComputes ].

Ltac computes_to_constructor :=
  first
    [ unfold refine; intros; apply @ReturnComputes
    | unfold refine; intros; apply @BindComputes
    | unfold refine; intros; apply @PickComputes ].

(* Class AbstractionRelation (R : Type) := { *)
(*   related : relation R *)
(* }. *)

(* Infix "≈" := related (at level 40). *)

(* Definition IsRefinementOf {R} `{AbstractionRelation R} *)
(*            (Am Bm : ∀ {i o}, R -> i -> Ensemble (R * o)) := *)
(*   ∀ rA rB, rA ≈ rB                        → *)
(*            ∀ rB' (i o : Type), Bm rB i ↝ (rB', o)  → *)
(*                                ∃ rA', Am rA i ↝ (rA', o) ∧ rA' ≈ rB'. *)

(* Infix "≃" := IsRefinementOf (at level 42). *)

(* Record ASig (R : Type) : Type := { *)
(*   m : forall {i o : Type}, R -> i -> Ensemble (R * o) *)
(* }. *)
