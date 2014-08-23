Require Export Coq.Init.Datatypes.
Require Export Coq.Arith.Compare_dec.

Fixpoint largest_elem (A : Type) (L : list (list A)) : nat :=
  (fix largest_elem' (A : Type) (n : nat) (L : list (list A)) : nat :=
    match L with
    | nil    => n
    | cons h t => if (gt_dec (length h) n) then largest_elem' A (length h) t
                                         else largest_elem' A n t
    end) A 0 L.

Function stratify_rec (A : Type) (lfs : list A) {measure largest_elem lfs} : Type.
  ...
with stratify_map xs := match xs with
  | nil => ...
  | head :: args => stratify_rec head :: stratify_map args
Proof.

Require Export Coq.Program.Tactics.
Require Export Coq.Program.Equality.
Require Export Coq.Logic.Eqdep.
Require Export Coq.Logic.EqdepFacts.

Notation "TYPE / I" := { x : TYPE & x -> I }.

Definition fiber {I : Type} (s : Type / I) (i : I) : Type :=
  match s with
    existT _ X f => { x : X & f x = i }
  end.

Hint Unfold fiber.

Definition unfiber {I : Type} (f : I -> Type) : Type / I :=
  existT _ {x : I & f x} (@projT1 _ _).

Hint Unfold unfiber.

Lemma edward2 : forall {X} y (f : y -> X),
  y = {x : X & {z : y & f z = x}}.
Proof.
  intros.
Admitted.

Lemma unfiber_fiber {I: Type} (s : Type / I) : unfiber (fiber s) = s.
Proof.
  autounfold.
  destruct s.
  apply eq_sigT_iff_eq_dep.
  apply eq_dep1_dep.
  refine (eq_dep1_intro _ _ _ _ _ _ _ _).
  apply (@edward2 I x i).
  unfold eq_rect, projT1.
Abort.

Lemma edward1 : forall {X} (f : X -> Type) (y : X),
  {x : {x : X & f x} & projT1 x = y} = f y.
Proof.
  intros.
  rewrite <- eq_sigT_sig_eq.
  rewrite (eq_rec_eq _ _ _ (f y)).
  simpl_existT.
  apply eq_sigT_eq_dep.
Defined.

Lemma fiber_unfiber {I: Type} (s : I -> Type) (i : I) : fiber (unfiber s) i = s i.
Proof.
  autounfold.
  rewrite edward.
  reflexivity.
Qed.
