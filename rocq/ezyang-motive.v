(** ** Elimination with a Motive (Conor McBride) *)

(** Edward: Elimination rules play an important role in computations over datatypes in
proof assistants like Coq. In his paper "Elimination with a Motive", Conor
McBride argued that "we should exploit a hypothesis not in terms of its
immediate consequences, but in terms of the leverage it exerts on an arbitrary
goal: we should give elimination a _motive_." In other words, proofs in
a refinement setting (backwards reasoning) should use their goals to guide
elimination.

The purpose of this document is to port Conor's pedagogical examples to Coq
notation, as well as give a tutorial about John Major equality (also
known as heterogenous equality.) This is basically an annotated version of
the first part of the paper--I reused most of the text, adding comments
here and there as necessary. *)

(** * Motivation *)

(** ** Conjunction and Disjunction *)

(** Conor: Undergraduates learning natural deduction are typically taught the following elimination
rules for conjunction and disjunction. *)

Lemma and_project_l : forall {A B : Prop}, A /\ B -> A. 
  tauto. Qed.
Lemma and_project_r : forall {A B : Prop}, A /\ B -> B.
  tauto. Qed.
Lemma or_elim : forall {A B C : Prop}, A \/ B -> (A -> C) -> (B -> C) -> C.
  destruct 1; tauto. Qed.

(** Students usually grasp the [and_project] rules easily, but find [or_elim]
frightening.  Edward: We can make this clear by attempting to do proofs in the forward
style: (here [False] is a stand-in for some goal which the student doesn't know
they are proving yet.) *)

Goal forall (A B : Prop), A /\ B -> False.
  intros. pose proof (and_project_l H).
Abort.

Goal forall (A B : Prop), A \/ B -> False.
  intros. try pose proof (or_elim H).
  (* Error: Cannot infer the implicit parameter C of or_elim. *)
Abort.

(** Coq has the same difficulty as our hypothetical student: the trouble is that
[C] appears from nowhere: students struggle to dream up of [C]'s which will eventually
lead to their goal. *)

(** When they learn proof by refinement (backwards reasoning), [or_elim] finally
makes sense: given [A \/ B], we can instantiate [C] with our goal, splitting it
into cases. *)

Goal forall (A B : Prop), A \/ B -> B \/ A.
  intros. apply (or_elim H); auto.
Qed.

(** The need to prove the goal is why we are eliminating [A \/ B]: the goal
is the motive for the elimination. We can choose the appropriate motive
precisely because '[C] appears from nowhere': [or_elim] is parametric in its motive.  *)

(** Elimination rules whose conclusion is a parameter--the motive variable--allow us
to exploit a hypothesis whatever the goal, just as 'left rules' in sequent calculus
analyse hypotheses regardless of what stands right of the turnstile. (Edward: To refresh your
sequent calculus, check out http://logitext.mit.edu/logitext.fcgi/tutorial scrolling to
the "Summary. Here are all the inference rules for first-order logic.") *)

(** In this light, the 'simplicity' of the and-project rules is less attractive:
we may only exploit [A /\ B] when we want to know [A] or we want to know [B]. I join the many
advocates of the 'Gentzenized' alternative (in reference to so-called 'Gentzen systems',
also known as sequent calculi), exploiting [A /\ B], whatever our motive [C]. *)

Lemma and_elim : forall {A B C : Prop}, A /\ B -> (A -> B -> C) -> C. tauto. Qed.

(** Edward: As an aside, on the other side of the Curry-Howard correspondence, the
projection rules are fst/snd, whereas the Gentzenized rule is uncurry. *)

(** ** Structural Induction and Recursion *)

(** 'Mathematical Induction' is another common example of elimination with a motive. *)

Lemma nat_induction : forall (P : nat -> Prop),
                        P 0 ->
                        (forall n, P n -> P (S n)) ->
                        forall n, P n. exact nat_ind. Qed.

(** Here, P stands for a family of propositions _indexed_ by a number. Not even
the most ardent 'forwardist' is bold enough to suggest that we should search our
collection of established facts for a pair related by [P] in order to add
[forall n, nat : P n] to that collection.  [nat_induction] needs a motive not
only because, like [or_elim], it splits the proof into cases, but also because
the abstract [n] being eliminated is instantiated in each case.  The point
of induction is not just to decompose a hypothesis but to simplify the goal:
where constructor symbols appear, computation can happen. *)

(** If we allow [P] to stand for a [nat]-indexed family of _types_ and supply the appropriate
computation behavior, induction becomes dependently typed primitive recursion,
supporting function on [n] whose return type depends on [n]. The explicit indexing
of [P] by numbers makes a strong connection to pattern matching and structural recursion.
We can expose these patterns even in simply typed examples by making a definition: *)

Definition Plus := fun (x y : nat) => nat.

Goal forall x y : nat, Plus x y.
  induction x.
  (* forall y : nat, Plus 0 y *)
  Focus 2.
  (*
  x : nat
  IHx : forall y : nat, Plus x y
  ============================
   forall y : nat, Plus (S x) y
  *)
Abort.

(** The return type of the goal reads like the left-hand side of a functional program
'under construction'. Induction splits our programming problem in two: we can
read off the instantiated patterns and, in the [S] case, the legitimate class of recursive
calls. *)

(** An elimination rule with an indexed motive variable [P] justifies a kind of pattern
analysis, 'matching' [P]'s arguments in the conclusion (the goal patterns) against
P's arguments in the premises (the subgoal patterns): [P]'s arguments in inductive
hypotheses (the recursion patterns) allow the corresponding recursive calls. To equip
an elimination rule with a computational behavior is to give its associated pattern
matching and structural recursion an operational semantics. *)

(* Illustrated, we have:

 forall (P : nat -> Prop),
                     P    0 ->    (* subgoal patterns *)
   (forall n, P n -> P (S n)) ->  (*      --"--       *)
             (* \__ recursion patterns *)
           forall n, P    n.      (* goal patterns *)

Or, more concretely:

                                    (forall y, Plus    0  y) -> (* subgoal patterns *)
  (forall x, (forall y, Plus x y) -> forall y, Plus (S x) y) -> (*      --"--       *)
             (* \__ recursion patterns *)
                                   forall x y, Plus    x  y     (* goal patterns *) *)

(** ** Relation Induction *)

(** Inductively defined relations may also be presented with an elimination rule
corresponding to induction on derivations.  For example, [<=] may be defined as follows: *)

Inductive le : nat -> nat -> Prop :=
  | le_refl : forall n, le n n
  | le_succ : forall m n, le m n -> le m (S n).
Hint Constructors le.

Definition le_induction :
  forall (P : nat -> nat -> Prop),
    (forall n, P n n) ->
    (forall m n, le m n -> P m n -> P m (S n)) ->
    forall {m n}, le m n -> P m n.
  exact le_ind.
Qed.

(** Relation induction is easy to apply if the eliminated hypothesis, [le m n], ranges
over the entire domain of the relation: we can choose [P] by naive 'undergraduate' textual
matching. *)

Goal forall m n, le m n -> le m n.
  induction 1; auto.
Qed.

(** However, if the hypothesis is _instantiated_, we still need a [P] indexed over
the whole domain, so we employ a well known goal transformation which I learned
from James McKinna--use a general [le m n], but constrain [m] and [n] with equations. *)

Goal forall (P : nat -> nat -> Prop) {m n}, le m n -> P m n.
  intro P. apply (le_induction (fun m n => P m n)).
Abort.

Goal forall {m}, le m 0 -> m = 0.
  intro. apply (le_induction _). (* not obvious *)
  trivial.
  (* In fact, Coq gets it wrong, picking (fun m n => m = n).
  This is not provable.

  m : nat
  ============================
   forall m0 n : nat, le m0 n -> m0 = n -> m0 = S n *)
Abort.

Goal forall {m}, le m 0 -> m = 0.
  intro. induction 1. trivial.
Abort.

(** We should generalize and add an equation. *)

Goal forall {m n}, le m n -> n = 0 -> m = 0.
  apply (le_induction (fun m n => n = 0 -> m = 0)); try inversion 3; trivial.
  (* Note: there is a typo in the paper: m <= n should not be included in P *)
Qed.

(** More generally, an elimination rule for an inductive relation, [R : forall (x : X) ..., Prop]
typically requires some [P : forall (x : X) ..., Prop] as motive. *)

(* 
Goal forall (y : Y) ..., R (t y) ... -> P y ... .
  assert (forall (x : X) (y : Y) ..., R x ... -> x = t y -> ... -> P x ...).
  apply (induction (fun x ... => forall (y : Y) ..., x = t y -> ... -> P y ...)).
*)

(** Plugging this [P] and the proof of [R (t y) ...] into the rule delivers a proof
of [P y ...] subject to the trivial equations [t y = t y ...]. This technique gives
a slightly clumsier for [P] than we chose for [m <= 0], which only constrains one argument,
so needs only one equation. It is not hard to see how to remove the unnecessary
equation. *)

(** Note that our chosen [P x ...] resembles the goal, but with some equations inserted
and [R (t y) ...] missing. [P] is not indexed over the proof of [R x ...], so elimination
tells us nothing about it: we an safely omit it from the motive. *)

(** ** Induction for Dependent Datatypes *)

(** The datatype analogue of inductively defined relations are dependent families
of datatypes, such as vectors--list of a given length--defined as follows: *)

Inductive Vect (A : Type) : nat -> Type :=
  | vnil : Vect A 0
  | vcons : forall {n}, A -> Vect A n -> Vect A (S n).

Lemma Vect_elim : forall {A : Type} (P : forall {n : nat}, Vect A n -> Type),
                         P (vnil A) ->
                         (forall {n} (x : A) {xs}, @P n xs -> @P (S n) (vcons A x xs)) ->
                         forall {n} (xs : Vect A n), @P n xs.
  exact Vect_rect.
Qed.

(* NB: Conor wants A to be inferred for constructors but explicit for the type;
Coq doesn't support this. *)

(** Proof terms for relations are interesting only for what they say about the
indices--their structure is unimportant. The terms in dependent datatypes are
the actual data. Corresponding, the motive [P] of [Vect_elim] is indexed not only over
the length of [n], but also over the vector itself: we care if a vector is [vnil] or [vcons].  On
the other hand, [P] is not indexed over the element type [A], which is parametric to
the entire inductive definition. *)

(** 'Constraint by equation' also works for instantiated datatypes. For example: *)

Definition VTail := fun {A : Type} {m : nat} (xxs : Vect A (S m)) => Vect A m.

Require Import JMeq.
Infix "==" := JMeq (at level 70, no associativity).

Goal forall {A : Type} {m : nat} (xxs : Vect A (S m)), VTail xxs.
  intro A.
  assert (forall {n : nat} (xs : Vect A n) {m : nat} (xxs : Vect A (S m)),
            n = S m -> xs == xxs (* !! *) -> VTail xxs) as X.
  apply (Vect_elim (fun {n : nat} (xs : Vect A n) =>
                      forall {m : nat} (xxs: Vect A (S m)),
                        n = S m -> xs == xxs (* !! *) -> VTail xxs)).

(** Solving the equations refutes the base case premises... *)

  (*
  A : Type
  ============================
   forall (m : nat) (xxs : Vect A (S m)),
   0 = S m -> vnil A == xxs -> VTail xxs
  *)
  inversion 1.

(** ...and reduces the step case to: *)

  (*
  A : Type
  ============================
   forall (n : nat) (x : A) (xs : Vect A n),
   (forall (m : nat) (xxs : Vect A (S m)), n = S m -> xs == xxs -> VTail xxs) ->
   forall (m : nat) (xxs : Vect A (S m)),
   S n = S m -> vcons A x xs == xxs -> VTail xxs
  *)
  inversion 2; subst. intro eq; rewrite <- eq.

(** The return type again shows the one pattern possible, and [xs]
is the tail we seek. *)

  (*
  ============================
   VTail (vcons A x xs)
  *)
  exact xs.

  (* ungeneralize the hypothesis... *)
  intros; apply (X (S m) xxs); auto.
Qed.

(** Unlike with [<=], our chosen [P] did quantify over the eliminated [xxs]--it
is matched to the [xs] in the goal patterns. Omitted this time is [A], parametric to the
definition, so kept parametric in the elimination.  We must be sensitive to these
distinctions in order to deliver appropriate behaviour, whatever the elimination rule. *)

(** * Equational Constraints and Dependent Types *)

(** By now, the eagle-eyed will have noticed that I write batched equations like
[x = t y ...] without worrying about type safety.  Indeed, in the above example, I
wrote [xs == xxs] where [xs : Vect A n] and [xxs : Vect A (S m)].  The conventional
Martin-Lof definition of [=] forbids such heterogeneous equations, relating elements of
different types. You can thus deduce that I am using an unconventional definition. *)

(** I define [==] as follows: *)

Print JMeq.

(*
Inductive JMeq (A : Type) (x : A) : forall B : Type, B -> Prop :=
    JMeq_refl : x == x
*)

Check JMeq_ind.

(*
JMeq_ind
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x == y -> P y
*)

(** This [==] can compare anything to [a], even if it is not in [A]. Correspondingly, we
may form heterogeneous sequences [s == t ...].  However, the introduction and
elimination rules follow the conventional _homogeneous_ definition: we shall
only treat something as an equal of a if its type really is [A]. I call this 'John Major'
equality, because it widens aspirations to equality without affecting the practical outcome. *)

(** If [s ...] and [t ...] are vectors in the same telescope (Edward: a telescope is a string of
abstractions, i.e. a generalized binding), then the leftmost equation [s1 == t1] is
homogeneous and thus vulnerable to elimination. *)

(** 'John Major' equality is equivalent to extending Martin-Lof equality with Altenkirch
and Streicher's 'uniqueness of identity proofs' axiom, often referred to as 'axiom K'.
It is clear that the new equality subsumes the old. On the other hand, we can write
a heterogeneous equation a = b as a homogeneous equation between pairs [(A, a) = (B, b)]
in the type [exists (T : Type), T]. Clearly [(A, a)] equals itself.  The elimination rule
follows if [a = a'] is a consequence of [(A, a) = (A, a')], and this is a wel known
variant of axiom K.  The details of this construction can be found in Conor McBride's thesis. *)

(** * The rest *)

(** Edward: In the rest of the paper, Conor McBride describes the tactic 'BasicElim', which
automatically performs the procedure we've seen alluded to above. *)

(** Fortunately for the average Coq user, a variant of this tactic has been implemented,
called 'dependent induction. We can see how it solves both of our previous problems. *)

Require Import Equality.

Goal forall {m}, le m 0 -> m = 0.
  intros m H. dependent induction H; trivial.
Qed.

Lemma vtail : forall {A : Type} {m : nat} (xxs : Vect A (S m)), VTail xxs.
  intros A m xxs. dependent induction xxs; trivial.
Qed.
Print Assumptions vtail.

(** As you can see, dependent induction uses JMeq internally. *)

(** There is more discussion about JMeq in Adam Chlipala's book CPDT:

    http://adam.chlipala.net/cpdt/html/Equality.html

JMeq (and axiom K) are very convenient assumptions to make, although in the light of
new developments such as Homotopy Type Theory, there may be interesting mathematics
to be done in type theories with models that do not validate axiom K. So while
some of the more recent, practically oriented dependently typed languages (e.g. Idris)
offer heterogenous equality as the default, there are also many reasons why Coq developments
will try to avoid using it.  Another downside of 'dependent induction' is that it is not
very fast, which can cause problems for large developments. *)
