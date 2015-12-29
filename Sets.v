Require Import
  Coq.Strings.String
  Coq.Sets.Ensembles.

Open Scope string_scope.

Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

(** The following Fiat ADT implements a very simple interface to sets, where
    the only operations are:

      1. Create an empty set.
      2. Add an element to a set.
      3. Check whether an element exists in a set.

    The ADT uses mathematical sets (Coq's Ensembles) to specify the meaning of
    these operations, which are understandably dead simple.

    The abstraction relation refines mathematical sets to lists, where lists
    represent a surjective mapping from sets _for the operations of insertion
    and checking for membership_. The abstraction relation does not consider
    any relationship between sets and lists outside of the ADT interface.

    Using this abstraction relation, we refine the specification to simple
    operations on lists, which are fully computable and thus can be extracted
    to OCaml or Haskell. *)

Section Sets.
  Context {A : Type}.

  (** The following specification defines the subset of our data
      representation that we implementation operations for. So long as only
      the ADT is used to manipulate that data, the semantics must be
      maintained. *)

  Definition spec : ADT _ := ADTRep (Ensemble A) {

    Def Constructor0 "new" : rep :=
      ret (Empty_set _),

    Def Method1 "insert" (r : rep) (x : A) : rep * unit :=
      ret (Add _ r x, tt),

    Def Method1 "member" (r : rep) (x : A) : rep * bool :=
      (* Read as: [b] is [true] iff [x] is [In] [r]. *)
      b <- { b | b = true <-> In _ r x };
      ret (r, b)

  }%ADTParsing.

  (** In order to use lists as our concrete representation, we require
      decidable equality on A to determine if an element already exists in the
      list. For the abstract representation, we only need to know that the
      element is a member of the set (which is not computable, but easily
      stated). *)

  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** The following is our "abstraction relation", and is the contract that
      refinement must fulfill in order for its proofs to succeed. If the
      contract is too strong, we lose the flexibility to make important
      optimization decisions; if the contract is too weak, we may not have
      enough information to complete the proof. For example, we intentionally
      say nothing here about duplicate members or ordering, since these
      details are not required by the ADT. *)

  Definition EnsembleAsList_AbsR (r_o : Ensemble A) (r_n : list A) :=
    forall x, In _ r_o x <-> List.existsb (A_eq_dec x) r_n.

  (** The value picked below (as the second argument to [refine]) decides how
      to implement "insertion" in terms of both our ADT specification, and the
      concrete list representation. Note: *any choice is possible for which
      the abstraction relation is provable*. For example:

        - [rcons] would be valid;

        - [cons] without any membership test is also valid, since "member"
          does not care that an element has been repeated, only that it is
          present;

        - manipulating the list before or after insertion is valid, so long as
          we don't drop existing elements that are not equal to [d].

      Freedom of my choice here is *directly* related to the chosen
      abstraction relation, and by extension to the defined specification,
      since proving refinement of the specification relies mainly on the
      information provided by the abstraction relation. Other aspects of the
      proof might take into account the monad laws, or other basic
      mathematical properties, but these alone can't't turn set-based
      definitions into list-based ones.

      What this means is that we first pick an abstraction relation to provide
      enough information to make the abstract -> concrete refinement proofs
      possible, and then we choose our particular refinements based on runtime
      needs. See the difference between [refine_Add_to_cons] and
      [refine_Add_to_cons_no_repeat] for example. *)

  Lemma refine_Add_to_cons (r_o : Ensemble A) (r_n : list A) (d : A) :
    EnsembleAsList_AbsR r_o r_n ->
    refine {r_n0 : list A | EnsembleAsList_AbsR (Add A r_o d) r_n0}
           (ret (cons d r_n)).
  Proof.
    unfold EnsembleAsList_AbsR.
    intros.
    apply refine_pick_val.
    split; intros; simpl.
      destruct H0.
        apply H in H0.
        rewrite H0.
        intuition.
      inversion H0.
      destruct (A_eq_dec x x); auto.
    simpl in H0.
    destruct (A_eq_dec x d); simpl in H0.
      rewrite e.
      apply Union_intror.
      apply In_singleton.
    apply H in H0.
    apply Union_introl.
    assumption.
  Qed.

  (** To show a refinement that is less CPU optimal, but more memory optimal,
      the following can be used in place of [refine_Add_to_cons] without
      changing the refinement proof in any other way. See the proofs for
      [sharpened_better_memory] below. *)

  Lemma refine_Add_to_cons_no_repeat (r_o : Ensemble A) (r_n : list A) (d : A) :
    EnsembleAsList_AbsR r_o r_n ->
    refine {r_n0 : list A | EnsembleAsList_AbsR (Add A r_o d) r_n0}
           (ret (if List.existsb (A_eq_dec d) r_n
                 then r_n
                 else cons d r_n)).
  Proof.
    unfold EnsembleAsList_AbsR.
    intros.
    apply refine_pick_val.
    split; intros.
      destruct (List.existsb _ r_n) eqn:Heqe.
        apply H.
        destruct H0.
          assumption.
        inversion H0.
        apply H.
        rewrite <- H1.
        rewrite Heqe.
        reflexivity.
      destruct H0.
        apply H in H0.
        simpl.
        rewrite H0.
        intuition.
      simpl.
      inversion H0.
      rewrite <- H1.
      destruct (A_eq_dec d d); auto.
    destruct (List.existsb _ r_n) eqn:Heqe.
      apply Union_introl.
      apply H in H0.
      assumption.
    destruct (A_eq_dec x d) eqn:Heqe2.
      apply Union_intror.
      rewrite e.
      apply In_singleton.
    apply Union_introl.
    apply H.
    simpl in H0.
    rewrite Heqe2 in H0.
    simpl in H0.
    assumption.
  Qed.

  (** The process of sharpening is one of proving that the semantics of the
      set-based specification above (see [spec]) can be faithfully carried
      over to the domain of lists, via the abstraction relation. If so, we
      arrive at a definition based on lists that is straightforward and can
      be extracted to executable code.

      The "goal" of each method subgoal below is to reduce the definition down
      to a single "ret" statement in its most reduced form. *)

  Theorem sharpened_better_cpu : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using EnsembleAsList_AbsR.

    (* constructor: new *)
    {
      (* NOTE: Although [finish honing] might solve this goal directly, it
        would generate a new subgoal at the end (from the call to
        [finish_SharpeningADT_WithoutDelegation]), requiring us to prove that
        [Empty_set] is equivalent to an empty list. Thus, the objective in
        these proofs is not just to complete the subgoals, but to reduce the
        goal to its simplest possible form, expressed purely in terms of our
        concrete representation (in this case, lists). *)

      simplify with monad laws; simpl.
      refine pick val nil.
        finish honing.
      split; intros;
      inversion H0.
    }

    (* method: insert *)
    {
      simplify with monad laws; simpl.
      rewrite (refine_Add_to_cons (r_n:=r_n));
        try assumption.
      simplify with monad laws; simpl.
      finish honing.
    }

    (* method: member *)
    {
      simplify with monad laws; simpl.
      refine pick val (List.existsb (A_eq_dec d) r_n).
        simplify with monad laws; simpl.
        refine pick val r_n;
          try assumption.
        simplify with monad laws; simpl.
        finish honing.
      split; intros; apply H0; assumption.
    }

    finish_SharpeningADT_WithoutDelegation.
  Defined.

  Theorem sharpened_better_memory : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using EnsembleAsList_AbsR.

    (* constructor: new *)
    {
      (* NOTE: Although [finish honing] might solve this goal directly, it
        would generate a new subgoal at the end (from the call to
        [finish_SharpeningADT_WithoutDelegation]), requiring us to prove that
        [Empty_set] is equivalent to an empty list. Thus, the objective in
        these proofs is not just to complete the subgoals, but to reduce the
        goal to its simplest possible form, expressed purely in terms of our
        concrete representation (in this case, lists). *)

      simplify with monad laws; simpl.
      refine pick val nil.
        finish honing.
      split; intros;
      inversion H0.
    }

    (* method: insert *)
    {
      simplify with monad laws; simpl.
      rewrite (refine_Add_to_cons_no_repeat (r_n:=r_n));
        try assumption.
      simplify with monad laws; simpl.
      finish honing.
    }

    (* method: member *)
    {
      simplify with monad laws; simpl.
      refine pick val (List.existsb (A_eq_dec d) r_n).
        simplify with monad laws; simpl.
        refine pick val r_n;
          try assumption.
        simplify with monad laws; simpl.
        finish honing.
      split; intros; apply H0; assumption.
    }

    finish_SharpeningADT_WithoutDelegation.
  Defined.

  (** We could perform even more sophisticated refinements, such as providing
      a fixed LRU cache. This would require choosing another abstraction
      relation, however, since otherwise we wouldn't know how the elements of
      the set relate to both the elements of the list and the members of the
      cache. *)

  Time Definition impl := Eval simpl in (projT1 sharpened_better_memory).
  Print impl.

  Definition newS    := "new".
  Definition insertS := "insert".
  Definition memberS := "member".

  Definition newSet : ComputationalADT.cRep impl :=
    Eval simpl in CallConstructor impl newS.
  Definition insertSet (r : ComputationalADT.cRep impl) (x : A) :
    ComputationalADT.cRep impl * unit :=
      Eval simpl in CallMethod impl insertS r x.
  Definition memberSet (r : ComputationalADT.cRep impl) (x : A) :
    ComputationalADT.cRep impl * bool :=
      Eval simpl in CallMethod impl memberS r x.

End Sets.

Extraction Language Haskell.

Extraction "Sets.hs" newSet insertSet memberSet.

(* Sample Haskell code to use this library's generated ADT:

     module Test where

     import Sets

     eqInt :: Int -> Int -> Sumbool
     eqInt x y = if x == y then Sets.Left else Sets.Right

     main :: IO ()
     main = do
         let s0 = newSet eqInt
         let Pair s1 Tt = insertSet eqInt s0 100
         let Pair _ b1 = memberSet eqInt s1 101
         putStrLn $ "b1 = " ++ case b1 of
             Sets.True  -> "True"
             Sets.False -> "False"
         let Pair _ b2 = memberSet eqInt s1 100
         putStrLn $ "b2 = " ++ case b2 of
             Sets.True  -> "True"
             Sets.False -> "False"

  Note that the Haskell *cannot become aware* of whether we've refined for
  optimized CPU or memory use, since the ADT interface is the only means it
  has for interacting with the data representation. *)
