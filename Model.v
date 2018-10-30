Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Streams.

Context `{C : Category}.
Context `(F : C ⟶ Sets).

Program Definition Streams : Category := {|
  obj := C;
  hom := fun x y => F x ~{Sets}~> F y;
  id  := fun x => id[F x]
|}.

Program Definition Streams_lift : C ⟶ Streams := {|
  fobj := fun x => x;
  fmap := fun x y f => {| morphism := fmap[F] f |}
|}.
Next Obligation.
  proper.
  destruct (fmap[F] f); simpl in *.
  now rewrite X.
Qed.
Next Obligation.
  proper.
  now sapply (@fmap_respects _ _ F).
Qed.
Next Obligation. sapply (@fmap_id _ _ F). Qed.
Next Obligation. sapply (@fmap_comp _ _ F). Qed.

(************************************************************************)

Context `{@Terminal C}.
Context `{TF : @TerminalFunctor _ _ F _ Sets_Terminal}.

Local Obligation Tactic := intros.

Global Program Instance Streams_Terminal : @Terminal Streams := {
  terminal_obj := @terminal_obj C _;
  one := fun _ => fmap[F] one;
  one_unique := fun x f g => _
}.
Next Obligation.
  simpl in *; intros.
  pose proof (iso_to_from (@fobj_one_iso _ _ _ _ _ TF)).
  simpl in X.
  rewrite <- X.
  symmetry.
  rewrite <- X.
  destruct (_ (g x0)), (_ (f x0)).
  reflexivity.
Qed.

(************************************************************************)

Context `{@Cartesian C}.
Context `{CF : @CartesianFunctor _ _ F _ _}.

Global Program Instance Streams_Cartesian : @Cartesian Streams := {
  product_obj := @product_obj C _;
  fork := fun x y z f g => _;
  exl  := fun x y => {| morphism := fmap[F] exl |};
  exr  := fun x y => {| morphism := fmap[F] exr |}
}.
Next Obligation.
  destruct f, g.
  morphism; intros.
  - sapply (@prod_in _ _ _ _ _ CF y z).
    intuition.
  - proper.
    now rewrite X.
Defined.
Next Obligation.
  proper.
  destruct F; simpl in *.
  destruct (fmap (x × y) x exl); simpl.
  now rewrite X.
Defined.
Next Obligation.
  proper.
  destruct F; simpl in *.
  destruct (fmap (x × y) y exr); simpl.
  now rewrite X.
Defined.
Next Obligation.
  repeat intro.
  unfold Streams_Cartesian_obligation_1.
  cbv [morphism].
  given (f : F x ~{Sets}~> F y × F z). {
    morphism; intro i.
    - exact (x0 i, x1 i).
    - simpl; intros.
      split; auto;
      destruct x0, x1; simpl;
      now rewrite X1.
  }
  given (g : F x ~{Sets}~> F y × F z). {
    morphism; intro i.
    - exact (y0 i, y1 i).
    - simpl; intros.
      split; auto;
      destruct y0, y1; simpl;
      now rewrite X1.
  }
  sapply (snd (@prod_in_inj _ _ _ _ _ CF x y z f g)).
  intuition.
Qed.
Next Obligation.
  unfold Streams_Cartesian_obligation_1.
  unfold Streams_Cartesian_obligation_2.
  unfold Streams_Cartesian_obligation_3.
  simpl.
  split; intros.
  - split; intros.
    + srewrite (@fmap_exl _ _ _ _ _ CF y z).
      rewrite X.
      now sapply (fst (iso_to_from (@fobj_prod_iso _ _ _ _ _ CF y z) (f x0, g x0))).
    + srewrite (@fmap_exr _ _ _ _ _ CF y z).
      rewrite X.
      now sapply (snd (iso_to_from (@fobj_prod_iso _ _ _ _ _ CF y z) (f x0, g x0))).
  - destruct X.
    destruct f, g, h; simpl in *.
    spose (iso_from_to (@fobj_prod_iso _ _ _ _ _ CF y z)) as H1.
    rewrite <- H1.
    eassert (Proper (equiv ==> equiv) (from (@fobj_prod_iso _ _ _ _ _ CF y z))).
      proper.
      now rewrite X.
    apply X.
    split; simpl.
    + rewrite <- e.
      now srewrite (@fmap_exl _ _ _ _ _ CF y z).
    + rewrite <- e0.
      now srewrite (@fmap_exr _ _ _ _ _ CF y z).
Qed.

End Streams.

(************************************************************************)

Require Import Category.Instance.Coq.

Section CoqStreams.

Definition Stream (A : Type) : Type := nat -> A.

Program Instance Stream_Setoid {a} : Setoid (Stream a) := {
  equiv := fun f g => ∀ x, f x = g x
}.
Next Obligation. equivalence; congruence. Defined.

Definition cons {A : Type} (x : A) (xs : Stream A) : Stream A :=
  fun i =>
    match i with
    | O => x
    | S i' => xs i'
    end.

Definition uncons {A : Type} (xs : Stream A) : A * Stream A :=
  (xs 0%nat, fun i => xs (S i)).

Lemma cons_uncons : ∀ A (x : A) xs, uncons (cons x xs) = (x, xs).
Proof.
  intros.
  unfold uncons, cons.
  f_equal.
Qed.

Lemma uncons_cons : ∀ A (xs : Stream A) (i : nat), prod_curry cons (uncons xs) i = xs i.
Proof.
  intros.
  unfold uncons, cons, prod_curry.
  induction i; simpl; auto.
Qed.

Lemma uncons_cons_ext : ∀ A (xs : Stream A), prod_curry cons (uncons xs) = xs.
Proof.
  intros.
  unfold uncons, cons, prod_curry.
  extensionality x.
  induction x; simpl; auto.
Qed.

Program Definition StreamFunctor : Coq ⟶ Sets := {|
  fobj := fun x : Type =>
    {| carrier := Stream x
     ; is_setoid := {| equiv := fun f g => ∀ x, f x = g x |} |};
  fmap := fun _ _ f => {| morphism := compose f |};
|}.
Next Obligation.
  equivalence.
  congruence.
Qed.
Next Obligation.
  proper.
  now rewrite H1.
Qed.

Global Program Instance StreamFunctor_Representable :
  @Representable _ StreamFunctor := {
  repr_obj := nat
}.
Next Obligation.
  isomorphism; simpl.
  - construct; simpl; auto.
    + morphism.
    + auto.
    + auto.
  - construct; simpl; auto.
    + morphism.
    + auto.
    + auto.
  - auto.
  - auto.
Defined.

Global Program Instance StreamFunctor_Terminal :
  @TerminalFunctor _ _ StreamFunctor _ _.
Next Obligation.
  isomorphism; simpl.
  - morphism; intro.
    exact tt.
  - morphism; intros.
      exact tt.
    proper.
  - simpl.
    now destruct (x x0).
  - simpl.
    now destruct x.
Defined.

Global Program Instance StreamFunctor_Cartesian :
  @CartesianFunctor _ _ StreamFunctor _ _.
Next Obligation.
  isomorphism; simpl.
  - morphism; intros.
    + split; intro i.
        exact (fst (H i)).
      exact (snd (H i)).
    + proper; now rewrite H.
  - morphism; intros.
    + intro i.
      exact (fst H i, snd H i).
    + proper; simpl in *.
      congruence.
  - simpl; auto.
  - simpl.
    now rewrite surjective_pairing.
Defined.

Definition scanr `(f : b -> a -> b) (q : b) (s : Stream a) : Stream b :=
  let fix go i :=
    match i with
    | O => q
    | S i' => f (go i') (s i)
    end in go.

Definition combine {a : Type} `{M : @Monoid Coq _ _ a} (s : Stream a) :=
  scanr (prod_uncurry (@mappend _ _ _ M)) (@mempty _ _ _ M (tt : unit : Type)) s.

Corollary combine_succ `{M : @Monoid Coq _ _ a} (s : Stream a) (i : nat) :
  combine (M:=M) s (S i) = @mappend _ _ _ M (combine (M:=M) s i, s (S i)).
Proof. auto. Qed.

Program Instance combine_Proper `{M : @Monoid Coq _ _ a} :
  Proper (equiv ==> equiv) (@combine _ M).
Next Obligation.
  repeat intro.
  unfold combine.
  induction x0; simpl in *; intros; auto.
  now rewrite H, IHx0.
Qed.

End CoqStreams.

(** A Mealy machine is a synchronous stream transformer. *)
Definition Mealy (a b : Type) :=
  (*           Z   Succ             *)
  { s : Type & s × (s × a -> s × b) }.

Program Definition mealy_denote `(computer : Mealy a b) :
  a ~{Streams StreamFunctor}~> b :=
  {| morphism :=
       let '(s0, f) := projT2 computer in
       fun input =>
         let fix output n :=
             f (match n with
                | O    => s0
                | S n' => fst (output n')
                end, input n)
         in snd ∘ output |}.
Next Obligation.
  proper.
  destruct computer; simpl.
  destruct p; simpl.
  f_equal.
  induction x0; simpl; intros; auto.
    now rewrite H.
  rewrite H.
  now rewrite IHx0.
Qed.
