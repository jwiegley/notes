Require Import Category.
Require Import Functor.

Set Implicit Arguments.

(* Formalization and exploration of hyper-functions. *)

Reserved Notation "f # g" (at level 69, right associativity).
Reserved Notation "f << h" (at level 68, left associativity).
Reserved Notation "f !-> h" (at level 99, left associativity).

Definition const {a b} (x : a) (_ : b) := x.

(* Hyperfunctions form a category, which when equipped with an embedding
   functor allow us to extend the set of operations by run and connect. *)

Section Hyperfunctions.

Context `(H : Category).
Context `(F : @Functor Sets H).

(* CoFixpoint fixpoint {a} (f : a -> a) : a := f (fixpoint f). *)

Class Hyper := {
    run     : forall {a}, (F a ~> F a) -> a;
    connect : forall {a b}, (a -> b) -> (F a ~> F b) -> (F a ~> F b)
      where "f << h" := (connect f h);

    self {a} : (F a ~> F a) := fmap id;
    invoke {a b} (f : F a ~> F b) (g : F b ~> F a) : b := run (f ∘ g);
    base {a b} (k : b) : (F a ~> F b) := fmap (const k);
    project {a b} (q : F a ~> F b) (x : a) : b := invoke q (base x);

    (* hyper_law_fix      : forall f, run (fmap f) = fixpoint f; *)

    hyper_law_distr    : forall {a b c} (f : b -> c) (g : a -> b) p q,
      (f << p) ∘ (g << q) = (@compose Sets _ _ _ f g) << (p ∘ q);

    hyper_law_lift     : forall {a b} (f : a -> b),
      fmap f = f << fmap f;

    hyper_law_run      : forall {a b} (f : a -> b) p q,
      run ((f << p) ∘ q) = f (run (q ∘ p))
}.

Definition mapH {a' b' a b} (r : a' -> a) (s : b -> b')
  (f : F a ~> F b) : (F a' ~> F b') := fmap s ∘ f ∘ fmap r.

Coercion project : Hyper >-> Funclass.

CoInductive HStream (a b : Type) : Type :=
  | HCons : (a -> b) -> HStream a b -> HStream a b.

CoInductive evilHStream := Nil.

Arguments HCons [a] [b] _ _.

Infix ":<<:" := HCons (at level 99, left associativity).

CoInductive hstream_eq {a b} : HStream a b -> HStream a b -> Prop :=
  | HStream_eq :
      forall h t1 t2, hstream_eq t1 t2 -> hstream_eq (HCons h t1) (HCons h t2).

Definition frob {a b} (s : HStream a b) : HStream a b :=
  match s with
    | HCons h t => HCons h t
  end.

Theorem frob_eq : forall {a b} (s : HStream a b), s = frob s.
  destruct s; reflexivity.
Defined.

Hypothesis hstream_equality : forall {a b} (x y : HStream a b),
  hstream_eq x y -> x = y.

CoFixpoint lift {a b} (f : a -> b) : HStream a b := f :<<: lift f.

CoFixpoint hcompose {a b c}
  (hf : HStream b c) (hg : HStream a b) : HStream a c :=
  match hf with
  | HCons f fs => match hg with
    | HCons g gs => (@compose Sets _ _ _ f g) :<<: (hcompose fs gs)
    end
  end.

Program Instance HStream_Category : Category := {
    ob := @ob Sets;
    hom := HStream;
    id := fun X => lift (@id Sets X);
    compose := @hcompose
}.
Obligation 1.
  apply hstream_equality. cofix.
  rewrite (frob_eq (hcompose f (lift (fun x : A => x)))).
  rewrite (frob_eq f).
  simpl.
  constructor.
  assumption.
Qed.

Definition invoke {a b} (h : Hyper a b) (i : Hyper b a) : b.
Proof.
  induction h.
    destruct i.
  destruct i.
  apply b0 in a0.
  assumption.
  apply IHh in i.
  apply b0.
  assumption.
Defined.

Definition konst {a b} (p : a) : Hyper b a := Hconst p.

Definition kons {a b} (f : a -> b) (q : Hyper a b) : Hyper a b :=
  match q with
    | Hconst b => 
    | H x x0 =>
  end
    
  H k (fun _ => f (invoke k q)).

Fixpoint happly {a b c} (f : Hyper b c) (g : Hyper a b) : Hyper a c :=
  H (fun k h => invoke f (happly g k)).

self :: Hyper a a
self = lift id

lift :: (a->b) -> Hyper a b
lift f = f << lift f

(<<) :: (a -> b) -> Hyper a b -> Hyper a b
f << q = Fn (\k -> f (invoke k q))

base :: a -> Hyper b a
base p = Fn (\k -> p)

run :: Hyper a a -> a
run f = invoke f self