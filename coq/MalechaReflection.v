Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

(**
 ** Speeding up Proofs with Computational Reflection
 ** Gregory Malecha
 ** gmalecha.github.io
 **
 **)

(* Proving Evenness *)
Inductive Even : nat -> Prop :=
| E0 : Even 0
| ESS : forall {n}, Even n -> Even (S (S n))
.

(** We can easily prove constants are even using these constructors.
 **)

Goal Even 0.
  exact E0.
Defined.

Goal Even 4.
  apply ESS. apply ESS. apply E0.
Defined.

(** However, when the constants get very large, things begin to slow
 ** down quite a bit. Eventually, we will get a stack overflow.
 **)
Example Even1000_constructor : Even 1000.
  Time repeat constructor.
Time Defined.
(** I will use `Defined` in this file to demonstrate the effect that
 ** computational reflection has on proofs. See my post on
 ** [Qed Considered Harmful](https://gmalecha.github.io/reflections/2017/qed-considered-harmful)
 ** for more discussion about this point.
 **)

(** The reason for this can be seen if we inspect the proof term.
 **)
Print Even1000_constructor.

(** Note that the entire proof is just a tower (of height 501) of `ESS`s
 ** (the final constructor is `E0`). This looks bad, but in reality it is
 ** much worse; which we can see if we enable more printing.
 **)
Set Printing All.
Print Even1000_constructor.
(** Note that the implicit `n` argument to `ESS` needs to be repeated at each
 ** level of the proof. Even in the case where this does not take any addiitional
 ** memory (assuming Coq is sharing common terms), there is considerable overhead
 ** to re-typechecking these terms and comparing them for equality.
 **)
Unset Printing All.


(** Two factors contribute to the bad performance.
 ** 1/ Building the proof (in Ltac).
 ** 2/ Checking the proof (in the kernel).
 **)

(** Using Gallina to Build the Proof *)

(** We can avoid the overhead of Ltac if we use a Gallina function to construct
 ** the proof term for us. This moves the expensive part of the computation
 ** from Ltac onto one of Coq's reduction mechanisms, e.g. `vm_compute`.
 ** This is morally similar to the tradeoff that [Mtac]() makes; however,
 ** Mtac's reduction mechanism bounces back and forth between Coq's reduction
 ** and intepreting the Mtac terms which makes it slightly slower.
 **)

(** The function to build the proof term follows from recursion over the
 ** natural number that we are proving `Even`. Note that we return an
 ** `option` since not all numbers are `Even`.
 **)
Fixpoint build_even (n : nat) : option (Even n) :=
  match n with (** this is a dependent pattern match *)
  | 0 => Some E0
  | 1 => None
  | S (S n) => match build_even n with
              | None => None
              | Some x => Some (ESS x)
              end
  end.

Ltac prove_even :=
  lazymatch goal with
  | |- Even ?n => let pf := eval vm_compute in (build_even n) in
                lazymatch pf with
                | Some ?pf => exact pf
                end
  end.

(** Using the above bit of Ltac, we use `build_even` to prove large
 ** numbers `Even`.
 **)
Theorem Even1000_Build : Even 1000.
  Time prove_even.
Time Defined.

(** Note that proving the goal is about 6 times faster, which can be attributed
 ** to the general mechanisms that Ltac implements. However, note that the
 ** checking of the proof term (which happens during `Defined`) takes the same
 ** amount of time. This shouldn't be surprising because the two proof terms
 ** are identical, which we can verify by printing it out.
 **)
Print Even1000_Build.




(** * Separating Checking and Witnessing *)

(** We can avoid constructing the large proof term if we phase separate the
 ** checking of the property (`Even`ness) and the generation of the proof
 ** term.
 **)

(** First, we write a simply typed function that checks the property.
 **)
Fixpoint check_even (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => check_even n
  end.

(** Then we prove that if the computation returns `true`, then it is possible
 ** to build a proof term. The constructive nature of the proof gives us a way
 ** construct the actual proof term.
 **)
Theorem check_even_sound
: forall {n},
    check_even n = true ->
    Even n.
Proof.
  (** Using `induction` here doen't work because we make our recursive
   ** call on `n-2` rather than `n-1`. This anonymous fixpoint mirrors the
   ** structure of the `check_even` function and allows us to prove
   ** the theorem.
   **)
  refine
    (fix recurse n : check_even n = true -> Even n :=
       match n with
       | 0 => _
       | 1 => _
       | S (S n) => let pf := recurse n in _
       end).
  - intro; constructor.
  - intro; exfalso. inversion H.
  - intro. apply ESS. apply pf. assumption.
Defined.

(** To use this phrasing to solve the goal, we first apply the soundness theorem
 ** which converts the goal into the computation. We can then use reduction
 ** (`vm_compute`) to reduce the computation to normal form, in this case
 ** `true = true` which we can solve by `reflexivity`.
 **)
Theorem Even1000_Reflect : Even 1000.
Proof.
  Time (
  apply check_even_sound;
  vm_compute;
  reflexivity). (** Play with running the tactic steps independently to get
                    a feeling of what is going on. *)
Time Defined.

(** Now both steps are very fast because we never need to build the proof term
 ** explicitly. Instead, we rely on Coq's (fast) reduction mechanism to check
 ** convertibility of two terms.
 ** To see the economical representation of our proof term, we can simply print
 ** it out.
 **)
Print Even1000_Reflect.
(** The `<:` represents a VM-cast in Coq and is the only indication that
 ** conversion is needed. Note that the term `@eq_refl bool true` is asserted
 ** to have type `check_even 1000 = true`, so the reduction needs to check
 ** that `check_even 1000` is /definitionally/ equal to `true`, which it is.
 **)

Ltac prove_even_r :=
  apply check_even_sound; vm_compute; reflexivity.

(**
 ** NOTE: It is essential that the theory that you apply computational
 ** reflection in has a cheap way to check convertibility. In proof assistants
 ** such as HOL, reduction proofs are witnessed explicitly (when proof
 ** generation is enabled) which means that the proofs produced by computational
 ** reflection will not be fast.
 **)

(** While on the surface, this proof is much better, in fact it is exactly the
 ** same proof. We can get Coq to check this for us, by asserting that *the
 ** proof terms* are equal.
 **)
Goal Even1000_constructor = Even1000_Build.
  reflexivity.
Defined.

Goal Even1000_Build = Even1000_Reflect.
  reflexivity.
Defined.

(** You can play around with this by applying `check_even_sound` to various
 ** values and reducing it.
 **)
Eval compute in @check_even_sound 4 eq_refl.

(** If you apply it to an odd number, you can see Coq reducing under the binder
 ** which is binding a proof of `false = true`.
 **)
Eval compute in @check_even_sound 5.

(** * Exploiting the Structure of the Term *)

(** We don't often look at very large numbers. Instead, we look at more compact
 ** (and meaningful) representations based on the facts we are reasoning about.
 ** For example suppose we had the following goal.
 **)

Goal Even (200 * 200 * 200).
  (** Note that `200 * 200` will reduce to a constant, so we
   ** can apply our automation above.
   **)
  Time prove_even_r.
Time Defined.
(** However, things are still a bit slow. *)

(** Of course, our Gallina functions can not inspect this sort of structure;
 ** doing so violate Gallina's notion of definitional equality and it would
 ** prevent us from really reasoning about values at all.
 ** To address the problem of variables, we build a syntactic
 ** representation of the problem, and 'reify' (or quote) the goal
 ** into that form so that computations can inspect its structure.
 **)

(** First, we define our language using an inductive data type *)
Inductive natS : Set :=
| Const : nat -> natS
| Plus : natS -> natS -> natS
| Mult : natS -> natS -> natS
.

(** Next we formalize the connection between the syntax and Gallina using
 ** a function.
 **)
Fixpoint natSD (s : natS) : nat :=
  match s with
  | Const n => n
  | Plus a b => natSD a + natSD b
  | Mult a b => natSD a * natSD b
  end.

(** Write a tactic to convert a Gallina term into a our language.
 **)
Ltac reify n :=
  lazymatch n with
  | ?A + ?B => let qA := reify A in
              let qB := reify B in
              uconstr:(Plus qA qB)
  | ?A * ?B => let qA := reify A in
              let qB := reify B in
              uconstr:(Mult qA qB)
  | _ => constr:(Const n)
  end.

(** Write the checker in Gallina by induction on the syntactic
 ** representation.
 **)
Fixpoint check_evenS (n : natS) : bool :=
  match n with
  | Const n => check_even n
  | Plus a b => andb (check_evenS a) (check_evenS b) (** NOTE: Incomplete *)
  | Mult a b => orb (check_evenS a) (check_evenS b)
  end.

(** Note that this function is incomplete, it only proves that `a + b` is `Even`
 ** if both `a` and `b` are `Even`. We can actually make it (relatively)
 ** complete but doing so is a bit more complicated, so I'll leave it as an
 ** exercise.
 **)

(** We're going to need to prove that `check_evenS` is sound so we start with
 ** some lemmas about `Even`ness.
 **)

(* Some lemmas *)
Theorem Even_plus : forall a b, Even a -> Even b -> Even (a + b).
Proof.
  induction 1; auto; constructor; auto.
Defined.

Lemma Even_a_plus_a : forall a, Even (a + a).
Proof.
  induction a; [ constructor | ].
  simpl. rewrite <- plus_n_Sm.
  constructor. assumption.
Defined.

Theorem Even_mult : forall a b, Even a -> Even (a * b).
Proof.
  induction 1.
  - constructor.
  - simpl.
    rewrite Nat.add_assoc.
    apply Even_plus; [ | assumption ].
    apply Even_a_plus_a.
Defined.

(** Prove soundness *)
Theorem check_evenS_sound
: forall n,
    check_evenS n = true ->
    Even (natSD n).
Proof.
  (** The proof proceeds by straight-forward structural induction on
   ** the syntactic represenation. We use the previous soundness theorem
   ** to justify the soundness of the `Const` case.
   **)
  induction n.
  - simpl. apply check_even_sound.
  - simpl. intros.
    apply andb_true_iff in H. destruct H.
    apply Even_plus; auto.
  - simpl. intros.
    apply orb_true_iff in H. destruct H.
    + apply Even_mult; auto.
    + rewrite Nat.mul_comm.
      apply Even_mult; auto.
Defined.

(** We can use the following tactic to reify the goal. *)
Ltac change_goal :=
  lazymatch goal with
  | |- Even ?N => let n := reify N in
                change (Even (natSD n))
  end.

(** We can then apply the tactic to put the goal in the right form
 ** and prove the theorem directly by appealing to the soundness of
 ** `check_evenS` and computation.
 **)
Goal Even (200 * 200 * 200 * 200).
  change_goal.
  apply check_evenS_sound.
  vm_compute.
  reflexivity.
Time Defined.
(** Note that this is a lot faster than the previous automation
 ** because the computation doesn't need to actually compute
 ** `200 * 200 * 200 * 200`; instead, the automation gets to inspect
 ** the structure (in this case 3 multiplications) in order to prove the
 ** goal.
 **)




(** * Supporting Open Terms **)

(** The limitation of this sort of reflection is that it fails for open terms.
 ** For example, after the `intros` the goal contains the variable `n` which
 ** could take on any value. This means that our Gallina functions that
 ** `match` on the number will get stuck `match`ing on `n`.
 **)
Goal forall n, Even n -> Even (S (S n)).
  intros.
  apply check_even_sound.
  vm_compute.
  (** stuck!! *)
Abort.


(** To address the problem of variables, we can extend our syntax with a
 ** way to represent "unknown" values.
 **)

(** To demo this (and to add a bit of variety to the talk) we're going to switch
 ** from proving `Even`ness to proving tautologies. As before, our automation is
 ** going to be incomplete, but we can make it complete if we make it more
 ** complex.
 **)

Require Import Quote.

(** Here is our language *)
Inductive prop : Set :=
| pTrue
| pFalse
| pAnd (_ _ : prop)
| pOr (_ _ : prop)
| pImpl (_ _ : prop)
| pOther (_ : index) (** uninterpreted symbols *)
.

(** The `pOther` constructor is what we're going to use represent unknown
 ** values. The `index` type is from the `Quote` library and is exactly the same
 ** type as `positive` (up to renaming). The basic idea is that we will use
 ** `index` as an "index" into a context mapping `index`es to values (in this
 ** case of type `Prop`). Our automation won't look into the table, but will be
 ** able to know if two `pOther` terms reference the same location (and are
 ** therefore equal).
 ** Note that while our reification of the goal will try to reuse indices in
 ** the table when values are repeated, we won't be able to prove that two
 ** different indices into the table mean different values. In practice, this
 ** means that we can really only prove a notion of relative completeness for
 ** reflective automation.
 **)

(** Just a simple opaque definition to represent an error message.
 **)
Definition not_found : Prop. (** "error message" *)
exact False.
Qed.

(** Again, a denotation function converts our syntax into a semantic value, in
 ** this case `Prop`.
 ** The `varmap Prop` is the context which contains the mapping from variables
 ** to `Prop`s. Like `index` it comes from the Quote library.
 **)
Fixpoint propD (ctx : varmap Prop) (p : prop) : Prop :=
  match p with
  | pTrue => True
  | pFalse => False
  | pAnd l r => propD ctx l /\ propD ctx r
  | pOr l r => propD ctx l \/ propD ctx r
  | pImpl l r => Basics.impl (propD ctx l) (propD ctx r)
    (* Basics.impl is a name for propositional implication. It is necessary here
     * to use the Quote library's `quote` tactic.
     *)
  | pOther i => varmap_find not_found i ctx
  end.

(** We'll need decidable equality on terms, so we implement an equality checker
 ** and prove it sound.
 **)
Fixpoint prop_eq (l r : prop) : bool :=
  match l , r with
  | pTrue , pTrue
  | pFalse , pFalse => true
  | pAnd a b , pAnd c d
  | pOr a b , pOr c d
  | pImpl a b , pImpl c d => prop_eq a c && prop_eq b d
  | pOther l , pOther r => index_eq l r
  | _ , _ => false
  end.

Lemma prop_eq_sound
: forall a b, prop_eq a b = true -> a = b.
Proof.
  induction a; destruct b;
    try solve [ eauto
              | inversion 1
              | simpl; intros; apply andb_true_iff in H; destruct H; f_equal; eauto ].
  - simpl. intros. f_equal.
    eapply index_eq_prop. auto.
Defined.

(** When reasoning about implication, we're going to need a represenation of
 ** our assumptions. For simplicity here, I'm going to use a `list`, but more
 ** sophisticated representations, e.g. discrimination trees, are possible and
 ** can improve performance dramatically for large problems.
 ** This predicate checks whether the `prop` exists in the context essentially
 ** implementing something analagous to the `assumption` tactic.
 **)
Definition knows (p : prop) (c : list prop) : bool :=
  existsb (prop_eq p) c.

(** The `learn` function extends the list of known facts to include one more
 ** fact. Here, we break up conjunctions so that we can prove theorems such as
 ** `(P /\ Q) -> P`. An alternative would be to add `P /\ Q` to the context
 ** and do this checking in `knows`.
 **)
Fixpoint learn (p : prop) (c : list prop) {struct p} : list prop :=
  match p with
  | pTrue => c
  | pFalse => p :: nil
  | pAnd l r => learn l (learn r c)
  | _ => p :: c (** for simplicity *)
  end.

(** This is the main piece of automation, it checks to see if a `prop` (`goal`)
 ** is provable from the list of known `prop`s.
 **)
Fixpoint provable (known : list prop) (goal : prop) {struct goal} : bool :=
  match goal with
  | pTrue => true
  | pFalse => knows pFalse known
  | pAnd l r => provable known l && provable known r
  | pOr l r => provable known l || provable known r
  | pImpl l r => provable (learn l known) r
  | pOther _ => knows goal known || knows pFalse known
  end.

(** Again, you will note that this automation is wildly incomplete. *)

(** In order to phrase soundness of our automation we need to provide a
 ** denotation function for contexts of known facts. The `All` function
 ** combines all the `prop`s in a list into a `prop` representing their
 ** conjunction, then we can connect this semantically using the same
 ** `propD` function we implemented above.
 **)
Definition All : list prop -> prop :=
  fold_right pAnd pTrue.

(** Soundness of `learn` says that if the original context is sound, and
 ** the fact that you are learning is sound, then the learned context is
 ** sound.
 **)
Lemma learn_sound
: forall ctx p c,
    propD ctx (All c) -> propD ctx p ->
    propD ctx (All (learn p c)).
Proof.
  induction p; simpl; intros; eauto.
  - destruct H0. eapply IHp1; auto.
Defined.

(** The soundness of `knows` means that if `knows` returns `true`, then
 ** the proposition is implied by the meaning of the context.
 **)
Lemma knows_sound
: forall ctx p c,
    knows p c = true ->
    propD ctx (All c) -> propD ctx p.
Proof.
  induction c.
  { simpl. inversion 1. }
  { simpl. intros.
    eapply orb_true_iff in H.
    destruct H.
    { eapply prop_eq_sound in H. subst. tauto. }
    { tauto. } }
Defined.

(** The soundness of `provable` is similar, it states that the goal is
 ** provable from the assumptions.
 **)
Lemma provable_sound
: forall g hyps,
    provable hyps g = true ->
    forall ctx, propD ctx (All hyps) -> propD ctx g.
Proof.
  induction g; simpl; intros; auto.
  - eapply knows_sound in H; eauto.
  - apply andb_true_iff in H. destruct H; eauto.
  - apply orb_true_iff in H. destruct H; eauto.
  - unfold Basics.impl in *. intros; eapply IHg2; eauto using learn_sound.
  - eapply orb_true_iff in H.
    destruct H.
    + eapply knows_sound in H; eauto.
    + eapply knows_sound in H; eauto.
      inversion H.
Defined.

(** The above theorem is general and phrased to have a good inductive structure
 ** but it isn't very convenient for applying. Instead, we write a specialized
 ** version to apply that fixes `hyps` to be the empty list.
 **)
Theorem provable_apply
: forall g,
    provable nil g = true ->
    forall ctx, propD ctx g.
Proof.
  intros. eapply provable_sound; eauto.
  compute; tauto.
Defined.

(** We can use the Quote library's `quote` tactic to change the goal into its
 ** quoted (reified) representation.
 ** Note that the argument to the `quote` tactic is the denotation function
 ** (`propD` in our case) which the tactic inspects to invert. While this works
 ** for simple problems, in practice more sophisticated reflection doesn't use
 ** `quote` due to the limitations of this mechanism. For example, we are
 ** getting around the limitation of `quote` note recognizing `->` by chaning
 ** `->` to `Basics.impl`.
 **)
Ltac quote_logic :=
  repeat match goal with
         | |- context [ ?A -> ?B ] => change (A -> B) with (Basics.impl A B)
         end;
  quote propD.

(** Using our tactic we can prove simple tautologies.
 ** Note that the way that our quoting works, we want to keep the `P` to the
 ** left of the arrow in the context, so that we quote
 ** `P -> P /\ True \/ False` rather than just `P /\ True \/ False` since the
 ** later is not provable by our automation since, in the later case, our
 ** automation will not get the information that `P` is provable.
 **)
Goal forall P : Prop, P -> P /\ True \/ False.
  intro P.
  quote_logic.
  eapply provable_apply.
  reflexivity.
Defined.

(** * Reflective Goal Simplification *)

(** In addition to proving goals entirely, we can also write reflective
 ** automation to simplify goals. By "simplifying a goal" `g`, I mean
 ** finding another (smaller, easier to reason about, etc.) goal `g'` that
 ** implies `g`.
 ** This is a pure generalization of solving the goal (where essentially `g'`
 ** is `True`).
 **)

(** A usual technique for writing this sort of automation is to write small
 ** functions for each case. For example, `pAnd'` simplifies `True /\ P` and
 ** `P /\ True` to `P` and `False /\ P` and `P /\ False` to `False`.
 **)
Definition pAnd' (a b : prop) : prop :=
  match a , b with
  | pTrue , _ => b
  | pFalse , _ => pFalse
  | _ , pTrue => a
  | _ , pFalse => pFalse
  | _ , _ => pAnd a b
  end.

(** In full generality, we could simplify `P /\ Q` to `P` if `P -> Q` or to `Q`
 ** if `Q -> P`. This is another reason to separate this function; we can
 ** improve it without affecting the full automation (as long as we update the
 ** soundness proof).
 **)

Theorem pAnd'_ok : forall ctx a b,
    propD ctx (pAnd' a b) <-> propD ctx (pAnd a b).
Proof.
  destruct a; destruct b; simpl; intros; tauto.
Defined.

(** Note that simplification proofs are often phrased using rewriting so we
 ** import the Morphisms library to get access to definitions such as `Proper`.
 **)
Require Import Coq.Classes.Morphisms.

(** A definition that lifts `->` to syntactic props. This is useful for using
 ** `Proper`.
 **)
Definition Impl ctx (a b : prop) : Prop :=
  propD ctx a -> propD ctx b.

Theorem Proper_pAnd'
: forall ctx, Proper (Impl ctx ==> Impl ctx ==> Impl ctx) pAnd'.
Proof.
  do 3 red. intros.
  red. repeat rewrite pAnd'_ok.
  simpl. unfold Impl in *. tauto.
Defined.

(** A more sophisticated version of the soundness of `pAnd'` will allow
 ** us to simplify `Q` assuming `P` when we simplify `P /\ Q`.
 **)
Theorem Proper_pAnd''
: forall ctx a a' b b',
    Impl ctx a a' ->
    (propD ctx a -> Impl ctx b b') ->
    Impl ctx (pAnd' a b) (pAnd' a' b').
Proof.
  intros. unfold Impl in *.
  repeat rewrite pAnd'_ok.
  simpl. tauto.
Defined.

(** Similar for \/ *)
Definition pOr' (a b : prop) : prop :=
  match a , b with
  | pTrue , _ => pTrue
  | pFalse , _ => b
  | _ , pTrue => pTrue
  | _ , pFalse => a
  | _ , _ => pOr a b
  end.

Theorem pOr'_ok : forall ctx a b,
    propD ctx (pOr' a b) <-> propD ctx (pOr a b).
Proof.
  destruct a; destruct b; simpl; intros; tauto.
Defined.

Theorem Proper_pOr'
: forall ctx, Proper (Impl ctx ==> Impl ctx ==> Impl ctx) pOr'.
Proof.
  do 3 red. intros.
  red. repeat rewrite pOr'_ok.
  simpl. unfold Impl in *. tauto.
Defined.

(** And similar for ->.
 ** Again, note that this is quite conservative.
 **)
Definition pImpl' (a b : prop) : prop :=
  match a , b with
  | pTrue , _ => b
  | pFalse , _ => pTrue
  | _ , pTrue => pTrue
  | _ , _ => pImpl a b
  end.

Theorem pImpl'_ok : forall ctx a b,
    propD ctx (pImpl' a b) <-> propD ctx (pImpl a b).
Proof.
  destruct a; destruct b; simpl; intros; unfold Basics.impl; try tauto.
Defined.

Theorem Proper_pImpl'
: forall ctx a b b',
    (propD ctx a -> Impl ctx b b') ->
    Impl ctx (pImpl' a b) (pImpl' a b').
Proof.
  unfold Impl. intros.
  repeat rewrite pImpl'_ok in *.
  simpl in *. unfold Basics.impl in *.
  intro. eapply H.
  simpl. unfold Impl in *. unfold Basics.impl in *.
  eauto. eauto.
Defined.

(** When we simplify a problem reflectively, we return a new term in our
 ** syntactic language that will imply the old one.
 **)
Fixpoint simplify (known : list prop) (goal : prop) {struct goal}
: prop :=
  match goal with
  | pTrue => pTrue
  | pAnd a b =>
    let a' := simplify known a in
    pAnd' a' (simplify (learn a' known) b)
  | pOr a b => pOr' (simplify known a) (simplify known b)
  | pImpl a b => pImpl' a (simplify (a :: known) b)
  | x => if knows x known then pTrue else x
  end.

(** The soundness of this automation is a bit more complex, but most of it
 ** simply appeals to the soundness of the automation for each of the symbols.
 **)
Theorem simplify_sound
: forall g hyps,
    let result := simplify hyps g in
    forall ctx, propD ctx (All hyps) ->
           propD ctx result ->
           propD ctx g.
Proof.
  induction g; simpl; intros; auto.
  - generalize (knows_sound ctx pFalse hyps); destruct (knows pFalse hyps);
      eauto. simpl. tauto.
  - eapply pAnd'_ok.
    eapply Proper_pAnd''. 3: eapply H0; eauto.
    + red. eauto.
    + red. intros.
      eapply IHg2; [ | eassumption ].
      eapply learn_sound; eauto.
  - eapply pOr'_ok.
    eapply Proper_pOr'. 3: eapply H0; eauto.
    + red. eauto.
    + red. eauto.
  - eapply pImpl'_ok.
    eapply Proper_pImpl'. 2: eauto.
    unfold Impl. intros.
    eapply IHg2; [ | eauto ].
    simpl. tauto.
  - generalize (knows_sound ctx (pOther i) hyps);
      destruct (knows (pOther i) hyps); eauto. simpl. tauto.
Defined.

(** As above, we write a simpler version of the soundness theorem that is
 ** easier to apply.
 **)
Theorem simplify_apply
: forall g g',
    simplify nil g = g' ->
    forall ctx, propD ctx g' -> (* this is the simplified goal *)
           propD ctx g.
Proof.
  intros. eapply simplify_sound with (hyps:=nil).
  - compute; tauto.
  - rewrite H; eauto.
Defined.

(** We can see how simplification works by looking at the following goal. *)

Goal forall P : Prop, P -> P /\ P /\ (True /\ True).
  intros P.
  (* Let's `intro HP` to make the goal alone unprovable. *)
  intro HP.
  quote_logic. (* quote the goal *)
  eapply simplify_apply.
  (* When we apply the lemma, we are left with two goals and one unification
   * variable.
   *)
  { (* Unfortunately, we can't use `vm_compute` to reduce goals that contain
     * unification variables, there are some tricks to get around this discussed
     * in my dissertation ([]()).
     *)
    compute.
    (* We solve the goal *after* computation so that the unification variable
     * is the simplified version.
     *)
    reflexivity. }
  (* If we've fully reduced our automation then at this point, the only terms
   * to simplify should be the denotation function. While we can use `simpl`
   * simplify this, a customized `cbv` is usually substantially faster *and*,
   * more importantly, will not simplify any of the terms in the variable
   * context.
   *)
  cbv beta iota zeta delta [ propD varmap_find ].
  (* When you have more sophisticated denotation functions, it can be annoying
   * to find the list of terms to reduce, but when the automation is a lot, it
   * improves performance a lot.
   *)

  (* At this point, we are back to the semantic version of the goal and this is
   * where the computational reflection ends. Note that if you wrap from
   * `quote_logic` to the above `cbv` in an Ltac tactic, then the fact that the
   * tactic uses reflection under the hood is completely hidden making it easy
   * to integrate into other, non-reflective, automation. For example,
   * `assumption`.
   *)
  assumption.
Defined.
