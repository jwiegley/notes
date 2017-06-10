Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.quote.Quote.

Generalizable All Variables.

Reserved Infix "⊓" (at level 40, left associativity).
Reserved Infix "⊔" (at level 36, left associativity).

Class Lattice (A : Set) := {
  meet : A -> A -> A where "x ⊓ y" := (meet x y);
  join : A -> A -> A where "x ⊔ y" := (join x y);

  meet_commutative : forall a b, a ⊓ b = b ⊓ a;
  meet_associative : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c);
  meet_absorptive  : forall a b, a ⊓ (a ⊔ b) = a;
  meet_idempotent  : forall a, a ⊓ a = a;

  join_commutative : forall a b, a ⊔ b = b ⊔ a;
  join_associative : forall a b c, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c);
  join_absorptive  : forall a b, a ⊔ (a ⊓ b) = a;
  join_idempotent  : forall a, a ⊔ a = a
}.

Infix "⊓" := meet (at level 40, left associativity).
Infix "⊔" := join (at level 36, left associativity).

Class Order (A : Set) := {
  ord : relation A;

  reflexive :> Reflexive ord;
  antisymmetric : forall {x y}, ord x y -> ord y x -> x = y;
  transitive :> Transitive ord
}.

Infix "≤" := ord (at level 50).

Class LOSet (A : Set) := {
  order :> Order A;
  lattice :> Lattice A;
  consistent: forall a b, a ≤ b <-> a = a ⊓ b
}.

Coercion is_lattice {A : Set} (O : LOSet A) : Lattice A := lattice.

Section Lattice.

Context `{l : LOSet A}.

Theorem meet_is_glb : forall a b : A,
  forall x, x ≤ a /\ x ≤ b <-> x ≤ a ⊓ b.
Proof.
  split; intros.
    intuition.
    apply consistent in H0.
    apply consistent in H1.
    apply consistent.
    rewrite <- meet_associative, <- H0.
    assumption.
  apply consistent in H.
  rewrite H; clear H.
  split; apply consistent.
    rewrite meet_associative.
    f_equal.
    rewrite meet_associative.
    rewrite (meet_commutative b a).
    rewrite <- meet_associative.
    rewrite meet_idempotent.
    reflexivity.
  rewrite meet_associative.
  f_equal.
  rewrite meet_associative.
  rewrite meet_idempotent.
  reflexivity.
Qed.

Theorem join_is_lub : forall a b : A,
  forall x, a ≤ x /\ b ≤ x <-> a ⊔ b ≤ x.
Proof.
  split; intros.
    intuition.
    apply consistent in H0.
    apply consistent in H1.
    apply consistent.
Admitted.

Set Decidable Equality Schemes.

Inductive Term : Set :=
  | Var  : nat  -> Term
  | Meet : Term -> Term -> Term
  | Join : Term -> Term -> Term.

Lemma Meet_acc_l x y : Meet x y <> x.
Proof.
  induction x;
  unfold not; intros;
  try discriminate.
  inversion H; subst.
  contradiction.
Qed.

Lemma Meet_acc_r x y : Meet x y <> y.
Proof.
  induction y;
  unfold not; intros;
  try discriminate.
  inversion H; subst.
  contradiction.
Qed.

Lemma Join_acc_l x y : Join x y <> x.
Proof.
  induction x;
  unfold not; intros;
  try discriminate.
  inversion H; subst.
  contradiction.
Qed.

Lemma Join_acc_r x y : Join x y <> y.
Proof.
  induction y;
  unfold not; intros;
  try discriminate.
  inversion H; subst.
  contradiction.
Qed.

Fixpoint length (t : Term) : nat :=
  match t with
  | Var n => 1
  | Meet t1 t2 => 1 + length t1 + length t2
  | Join t1 t2 => 1 + length t1 + length t2
  end.

Fixpoint depth (t : Term) : nat :=
  match t with
  | Var n => 0
  | Meet t1 t2 => 1 + max (depth t1) (depth t2)
  | Join t1 t2 => 1 + max (depth t1) (depth t2)
  end.

Inductive Subterm : Term -> Term -> Prop :=
  | Meet1 : forall t1 t2, Subterm t1 (Meet t1 t2)
  | Meet2 : forall t1 t2, t1 <> t2 -> Subterm t2 (Meet t1 t2)
  | Join1 : forall t1 t2, Subterm t1 (Join t1 t2)
  | Join2 : forall t1 t2, t1 <> t2 -> Subterm t2 (Join t1 t2).

Definition Subterm_inv_t : forall x y, Subterm x y -> Prop.
Proof.
  intros [] [] f;
  match goal with
  | [ H : Subterm ?X (Meet ?X ?Z) |- Prop ] =>
    exact (f = Meet1 _ _)
  | [ H : Subterm ?X (Join ?X ?Z) |- Prop ] =>
    exact (f = Join1 _ _)
  | [ H : Subterm ?X (Meet ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec Y X) as [e|e]; subst;
    [ exact (f = Meet1 _ _)
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Meet2 Y X e)
      | exact False ] ]
  | [ H : Subterm ?X (Join ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec Y X) as [e|e]; subst;
    [ exact (f = Join1 _ _)
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Join2 Y X e)
      | exact False ] ]
  | _ => exact False
  end.
Defined.

Theorem UIP_dec_not : forall (A : Type),
  (forall x y:A, {x = y} + {x <> y}) ->
  forall (x y:A) (p1 p2:x <> y), p1 = p2.
Proof.
  intros.
  unfold not in *.
  (* jww (2017-06-10): Is there any way to avoid an axiom here? *)
  Require Import FunctionalExtensionality.
  extensionality p.
  subst; contradiction.
Qed.

Print Assumptions UIP_dec_not.

Corollary Subterm_inv x y f : Subterm_inv_t x y f.
Proof.
  pose proof Term_eq_dec.
  destruct f, t1, t2; simpl;
  repeat destruct (Term_eq_dec _ _); subst;
  unfold eq_rect_r;
  try (rewrite e || rewrite <- e);
  try congruence;
  try rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto;
  f_equal;
  apply UIP_dec_not; auto.
Qed.

Program Instance Subterm_StrictOrder : StrictOrder Subterm.
Next Obligation.
  repeat intro.
  pose proof (Subterm_inv _ _ H).
  inversion H; subst; simpl in *.
  - now apply (Meet_acc_l x t2).
  - now apply (Meet_acc_r t1 x).
  - now apply (Join_acc_l x t2).
  - now apply (Join_acc_r t1 x).
Qed.
Next Obligation.
  repeat intro.
  pose proof (Subterm_inv _ _ H).
  pose proof (Subterm_inv _ _ H0).
  inversion H; subst; simpl in *;
  inversion H0; subst; simpl in *.
  (* jww (2017-06-10): At least the way that Subterm is currently defined, it
     is not transitive. *)
Admitted.

Lemma Subterm_wf : well_founded Subterm.
Proof.
  constructor; intros.
  inversion H; subst; simpl in *.
  - induction y, t2; simpl in *;
    constructor; intros;
    inversion H0; subst; clear H0;
    try (apply IHy1; constructor);
    try (apply IHy2; constructor).
  - induction y, t1; simpl in *;
    constructor; intros;
    inversion H1; subst; clear H1.
    destruct y1.
    destruct (Term_eq_dec (Var n) (Var n0)).
    apply IHy1.
    constructor.
    try (apply IHy1; constructor);
    try (apply IHy2; constructor).

Reserved Notation "〚 t 〛 env" (at level 9).

Fixpoint eval (t : Term) (env : nat -> A) : A :=
  match t with
  | Var n => env n
  | Meet t1 t2 =>〚t1〛env ⊓〚t2〛env
  | Join t1 t2 =>〚t1〛env ⊔〚t2〛env
  end where "〚 t 〛 env" := (eval t env).

Definition Leq   (s t : Term) : Prop := forall env, 〚s〛env ≤ 〚t〛env.
Definition Equiv (s t : Term) : Prop := forall env, 〚s〛env = 〚t〛env.

Reserved Infix "≲" (at level 30).

Definition R := symprod Term Term Subterm Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Program Fixpoint leq (p : Term * Term) {wf R p} :
  { b : bool | b = true -> Leq (fst p) (snd p) } :=
  match p with
  | (s, t) =>
    let leqb x y := proj1_sig (leq (x, y)) in
    match (s, t) with
    | (Var i, Var j)           => nat_eq_bool i j
    | (Join s1 s2, t)          => leqb s1 t &&& leqb s2 t
    | (s, Meet t1 t2)          => leqb s t1 &&& leqb s t2
    | (Var m, Join t1 t2)      => leqb s t1 ||| leqb s t2
    | (Meet s1 s2, Var n)      => leqb s1 t ||| leqb s2 t
    | (Meet s1 s2, Join t1 t2) => leqb s1 t ||| leqb s2 t ||| leqb s t1 ||| leqb s t2
    end
  end where "s ≲ t" := (leq (s, t)).
Next Obligation.
  destruct (leq (x, t1)).
    constructor.
    admit.
  simpl in *.
  unfold Leq in l0.
   apply left_sym.
Admitted.
Next Obligation.
  unfold Leq; intros; simpl.
  destruct (nat_eq_bool i j) eqn:Heqe; simpl in H; subst.
  rewrite y.
  reflexivity.
Qed.
Next Obligation.
  unfold Leq; intros; simpl.
  inversion Heq_p; subst.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  unfold MR, R; simpl.
Admitted.

Notation "s ≲ t" := (leq (s, t)).

Import ListNotations.

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac allVars xs m j e :=
  match e with
  | m ?e1 ?e2 =>
    let xs := allVars xs m j e1 in
    allVars xs m j e2
  | j ?e1 ?e2 =>
    let xs := allVars xs m j e1 in
    allVars xs m j e2
  | _ => addToList e xs
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => O
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(S n)
  end.

Ltac reifyTerm env m j t :=
  match t with
  | m ?X1 ?X2 =>
    let r1 := reifyTerm env m j X1 in
    let r2 := reifyTerm env m j X2 in
    constr:(Meet r1 r2)
  | j ?X1 ?X2 =>
    let r1 := reifyTerm env m j X1 in
    let r2 := reifyTerm env m j X2 in
    constr:(Join r1 r2)
  | ?X =>
    let n := lookup X env in
    constr:(Var n)
  end.

Lemma leq_correct : forall t u : Term,
  Is_true (` (t ≲ u)) -> forall env, 〚t〛env ≤ 〚u〛env.
Proof.
  intros.
  induction t, u; simpl in *.
Admitted.

Ltac functionalize xs :=
  let rec loop n xs' :=
    match xs' with
    | (?x, tt) => constr:(fun _ : nat => x)
    | (?x, ?xs'') =>
      let f := loop (S n) xs'' in
      constr:(fun m : nat => if m =? n then x else f m)
    end in
  loop 0 xs.

Ltac reify m j :=
  match goal with
  | [ |- ?S ≤ ?T ] =>
    let xs  := allVars tt m j S in
    let xs' := allVars xs m j T in
    let r1  := reifyTerm xs' m j S in
    let r2  := reifyTerm xs' m j T in
    let env := functionalize xs' in
    pose xs';
    pose env;
    pose r1;
    pose r2;
    change (〚r1〛env ≤ 〚r2〛env);
    apply leq_correct;
    vm_compute
  end.

Ltac lattice := reify meet join.

Lemma median_inequality : forall x y z : A,
  (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x).
Proof.
  intros.
  lattice.
Admitted.

End Lattice.
