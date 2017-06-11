Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.quote.Quote.
Require Import Coq.Wellfounded.Lexicographic_Product.

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

Class LOSet {A : Set} `(@Order A) `(@Lattice A) := {
  meet_consistent : forall a b, a ≤ b <-> a = a ⊓ b;
  join_consistent : forall a b, a ≤ b <-> b = a ⊔ b
}.

Section Lattice.

Context `{O : Order A}.
Context `{L : Lattice A}.
Context `{@LOSet A O L}.

Theorem meet_is_glb : forall a b : A,
  forall x, x ≤ a /\ x ≤ b <-> x ≤ a ⊓ b.
Proof.
  split; intros.
    intuition.
    apply meet_consistent in H1.
    apply meet_consistent in H2.
    apply meet_consistent.
    rewrite <- meet_associative, <- H1.
    assumption.
  apply meet_consistent in H0.
  rewrite H0; clear H0.
  split; apply meet_consistent.
    rewrite meet_associative.
    rewrite (meet_commutative (a ⊓ b) a).
    rewrite <- (meet_associative a).
    rewrite meet_idempotent.
    reflexivity.
  rewrite meet_associative.
  rewrite meet_associative.
  rewrite meet_idempotent.
  reflexivity.
Qed.

Theorem meet_prime : forall a b : A,
  forall x, a ≤ x \/ b ≤ x -> a ⊓ b ≤ x.
Proof.
  intros.
  destruct H0;
  apply meet_consistent in H0;
  apply meet_consistent; [rewrite meet_commutative|];
  rewrite meet_associative;
  rewrite <- H0; reflexivity.
Qed.

Theorem join_is_lub : forall a b : A,
  forall x, a ≤ x /\ b ≤ x <-> a ⊔ b ≤ x.
Proof.
  split; intros.
    intuition.
    apply join_consistent in H1.
    apply join_consistent in H2.
    apply join_consistent.
    rewrite join_associative, <- H2.
    assumption.
  apply join_consistent in H0.
  rewrite H0; clear H0.
  split; apply join_consistent.
    rewrite <- join_associative.
    rewrite <- join_associative.
    rewrite join_idempotent.
    reflexivity.
  rewrite (join_commutative a b).
  rewrite <- join_associative.
  rewrite <- join_associative.
  rewrite join_idempotent.
  reflexivity.
Qed.

Theorem join_prime : forall a b : A,
  forall x, x ≤ a \/ x ≤ b -> x ≤ a ⊔ b.
Proof.
  intros.
  destruct H0;
  apply join_consistent in H0;
  apply join_consistent; [|rewrite join_commutative];
  rewrite <- join_associative;
  rewrite <- H0; reflexivity.
Qed.

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
  inversion H0; subst.
  contradiction.
Qed.

Lemma Meet_acc_r x y : Meet x y <> y.
Proof.
  induction y;
  unfold not; intros;
  try discriminate.
  inversion H0; subst.
  contradiction.
Qed.

Lemma Join_acc_l x y : Join x y <> x.
Proof.
  induction x;
  unfold not; intros;
  try discriminate.
  inversion H0; subst.
  contradiction.
Qed.

Lemma Join_acc_r x y : Join x y <> y.
Proof.
  induction y;
  unfold not; intros;
  try discriminate.
  inversion H0; subst.
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
  | Meet2 : forall t1 t2, Subterm t2 (Meet t1 t2)
  | Join1 : forall t1 t2, Subterm t1 (Join t1 t2)
  | Join2 : forall t1 t2, Subterm t2 (Join t1 t2).

Definition Subterm_inv_t : forall x y, Subterm x y -> Prop.
Proof.
  intros [] [] f;
  match goal with
  | [ H : Subterm ?X (Meet ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Meet1 _ _ \/ f = Meet2 _ _)
      | exact (f = Meet1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Meet2 _ _)
      | exact False ] ]
  | [ H : Subterm ?X (Join ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Join1 _ _ \/ f = Join2 _ _)
      | exact (f = Join1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Join2 _ _)
      | exact False ] ]
  | _ => exact False
  end.
Defined.

Corollary Subterm_inv x y f : Subterm_inv_t x y f.
Proof.
  pose proof Term_eq_dec.
  destruct f, t1, t2; simpl;
  repeat destruct (Term_eq_dec _ _); subst;
  try (rewrite e || rewrite <- e);
  try (rewrite e0 || rewrite <- e0);
  try congruence;
  try rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto; simpl; intuition;
  try rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto; simpl; intuition.
Qed.

Program Instance Subterm_Irreflexive : Irreflexive Subterm.
Next Obligation.
  repeat intro.
  pose proof (Subterm_inv _ _ H0).
  inversion H0; subst; simpl in *.
  - now apply (Meet_acc_l x t2).
  - now apply (Meet_acc_r t1 x).
  - now apply (Join_acc_l x t2).
  - now apply (Join_acc_r t1 x).
Qed.

Lemma Subterm_wf : well_founded Subterm.
Proof.
  constructor; intros.
  inversion H0; subst; simpl in *;
  induction y;
  induction t1 || induction t2;
  simpl in *;
  constructor; intros;
  inversion H1; subst; clear H1;
  try (apply IHy1; constructor);
  try (apply IHy2; constructor).
Defined.

Reserved Notation "〚 t 〛 env" (at level 9).

Fixpoint eval (t : Term) (env : nat -> A) : A :=
  match t with
  | Var n => env n
  | Meet t1 t2 => 〚t1〛env ⊓ 〚t2〛env
  | Join t1 t2 => 〚t1〛env ⊔ 〚t2〛env
  end where "〚 t 〛 env" := (eval t env).

Definition Leq   (s t : Term) : Prop := forall env, 〚s〛env ≤ 〚t〛env.
Arguments Leq _ _ /.

(* Note that Equiv can be computed from Leq. *)
Definition Equiv (s t : Term) : Prop := forall env, 〚s〛env = 〚t〛env.
Arguments Equiv _ _ /.

Reserved Infix "≲" (at level 30).

Definition R := symprod Term Term Subterm Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Ltac meets_and_joins leq :=
  repeat destruct (leq (_, _) _);
  simpl in *;
  subst;
  repeat match goal with
  | [ H : (_, _) = (_, _) |- _ ] => progress (inversion H; subst)
  | [ H : bool |- _ ] => destruct H
  end;
  try discriminate;
  simpl in *;
  repeat match goal with
  | [ |- _ ⊔ _ ≤ _ ] => apply join_is_lub; split; firstorder idtac
  | [ |- _ ≤ _ ⊔ _ ] => apply join_prime; firstorder idtac
  | [ |- _ ≤ _ ⊓ _ ] => apply meet_is_glb; split; firstorder idtac
  | [ |- _ ⊓ _ ≤ _ ] => apply meet_prime; firstorder idtac
  end.

Local Obligation Tactic :=
  program_simpl; try (constructor; constructor).

Set Transparent Obligations.

(* Whitman's decision procedure. *)
Program Fixpoint leq (p : Term * Term) {wf R p} :
  { b : bool | b = true -> Leq (fst p) (snd p) } :=
  match p with
  (* 1. If s = Var i and t = Var j, then s ≲ t holds iff i = j. *)
  | (Var i, Var j) => nat_eq_bool i j

  (* 2. If s = Join s1 s2, then s ≲ t holds iff s1 ≲ t and s2 ≲ t. *)
  | (Join s1 s2, t) =>
    exist _ (proj1_sig (leq (s1, t)) &&& proj1_sig (leq (s2, t))) _

  (* 3. If t = Meet t1 t2, then s ≲ t holds iff s ≲ t1 and s ≲ t2. *)
  | (s, Meet t1 t2) =>
    exist _ (proj1_sig (leq (s, t1)) &&& proj1_sig (leq (s, t2))) _

  (* 4. If s = Var i and t = Join t1 t2, then s ≲ t holds iff s ≲ t1 or s ≲ t2. *)
  | (Var i, Join t1 t2) =>
    exist _ (proj1_sig (leq (Var i, t1)) ||| proj1_sig (leq (Var i, t2))) _

  (* 5. If s = Meet s1 s2 and t = Var i, then s ≲ t holds iff s1 ≲ t or s2 ≲ t. *)
  | (Meet s1 s2, Var i) =>
    exist _ (proj1_sig (leq (s1, Var i)) ||| proj1_sig (leq (s2, Var i))) _

  (* 6. If s = Meet s1 s2 and t = Join t1 t2, then s ≲ t holds iff s1 ≲ t or
        s2 ≲ t or s ≲ t1 or s ≲ t2. *)
  | (Meet s1 s2, Join t1 t2) =>
    exist _ (proj1_sig (leq (s1, Join t1 t2)) |||
             proj1_sig (leq (s2, Join t1 t2)) |||
             proj1_sig (leq (Meet s1 s2, t1)) |||
             proj1_sig (leq (Meet s1 s2, t2))) _
  end.
Next Obligation.
  destruct (nat_eq_bool i j); simpl in *; subst.
  rewrite y; reflexivity.
Defined.
Next Obligation. meets_and_joins leq. Defined.
Next Obligation. meets_and_joins leq. Defined.
Next Obligation. meets_and_joins leq. Defined.
Next Obligation. meets_and_joins leq. Defined.
Next Obligation.
  repeat destruct (leq (_, _)); simpl in *.
  destruct x.  apply meet_prime; left;  apply o;  reflexivity.
  destruct x0. apply meet_prime; right; apply o0; reflexivity.
  destruct x1. apply join_prime; left;  apply o1; reflexivity.
  destruct x2. apply join_prime; right; apply o2; reflexivity.
  discriminate.
Defined.
Next Obligation.
  apply wf_symprod;
  apply Subterm_wf.
Defined.

Example speed_test :
  ` (leq (Meet (Var 0) (Var 1), Join (Var 0) (Var 1))) = true.
Proof. reflexivity. Qed.

Notation "s ≲ t" := (leq (s, t)) (at level 30).

Definition leq_correct {t u : Term} (Heq : ` (t ≲ u) = true) :
  forall env, 〚t〛env ≤ 〚u〛env := proj2_sig (leq (t, u)) Heq.

End Lattice.

Notation "〚 t 〛 env" := (@eval _ _ t env) (at level 9).
Notation "s ≲ t" := (@leq _ _ _ _ (s, t)) (at level 30).

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

Ltac allVars xs e :=
  match e with
  | ?e1 ⊓ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | ?e1 ⊔ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | _ => addToList e xs
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => O
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(S n)
  end.

Ltac reifyTerm env t :=
  match t with
  | ?X1 ⊓ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Meet r1 r2)
  | ?X1 ⊔ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Join r1 r2)
  | ?X =>
    let n := lookup X env in
    constr:(Var n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    match xs' with
    | (?x, tt) => constr:(fun _ : nat => x)
    | (?x, ?xs'') =>
      let f := loop (S n) xs'' in
      constr:(fun m : nat => if m =? n then x else f m)
    end in
  loop 0 xs.

Ltac reify :=
  match goal with
  | [ |- ?S ≤ ?T ] =>
    let xs  := allVars tt S in
    let xs' := allVars xs T in
    let r1  := reifyTerm xs' S in
    let r2  := reifyTerm xs' T in
    let env := functionalize xs' in
    (* pose xs'; *)
    (* pose env; *)
    (* pose r1; *)
    (* pose r2; *)
    change (〚r1〛env ≤ 〚r2〛env)
  end.

Ltac lattice := reify; apply leq_correct; vm_compute; auto.

Example sample_1 `{LOSet A} : forall a b : A,
  a ≤ a ⊔ b.
Proof. intros; lattice. Qed.

Lemma running_example `{LOSet A} : forall a b : A,
  a ⊓ b ≤ a ⊔ b.
Proof.
  intros a b.
  rewrite meet_consistent.
  rewrite meet_associative.
  rewrite join_commutative.
  rewrite meet_absorptive.
  reflexivity.
Qed.

Lemma running_example' `{LOSet A} : forall a b : A,
  a ⊓ b ≤ a ⊔ b.
Proof. intros; lattice. Qed.

Lemma median_inequality `{LOSet A} : forall x y z : A,
  (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x).
Proof. intros; lattice. Qed.
