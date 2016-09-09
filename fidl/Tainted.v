Require Import
  Hask.Data.Functor
  Hask.Control.Monad
  FIDL.Tactics
  FIDL.Comp.

Definition Tainted (m : Type -> Type) (A : Type) (P : Comp A) : Type :=
  m ({ x : A | P ↝ x } + A)%type.

Definition computes_map `{P : Comp A} `(f : A -> B) :
  forall v : A, P ↝ v -> fmap f P ↝ f v :=
  fun (v : A) (H : P ↝ v) => ex_intro _ v (conj H (In_singleton B (f v))).

Import EqNotations.
Import FunctorLaws.

Lemma id_expansion `{P : Comp A} : forall (v : A),
  P ↝ v -> fmap[Comp] id P ↝ id v.
Proof.
  intros.
  rewrite fmap_id.
  apply H.
Defined.

Lemma computes_map_id `{P : Comp A} : forall (v : A) (H : P ↝ v),
  computes_map id v H = id_expansion _ H.
Proof.
  intros.
  unfold computes_map, id_expansion.
  unfold id. simpl.
  auto.
Abort.

Section Test.
Context `{Monad m}.
Goal Tainted m (fun n : nat => n < 10).
Proof.
  unfold Tainted.
  apply pure.
  apply inl.
  exists 0.
  constructor.
  omega.
Qed.
End Test.

Lemma tmap_id_eq `(f : forall A : Type, Comp A -> Type) :
  forall (a : Type) (P : Comp a), f a P = f a (fmap id P).
Proof.
  intros.
  rewrite fmap_id.
  reflexivity.
Qed.

Lemma tmap_comp_eq `(f : forall A : Type, Comp A -> Type) :
  forall (a b c : Type) (P : Comp a) (g : a -> b) (k : b -> c),
    f c ((fmap k \o fmap g) P) = f c (fmap (k \o g) P).
Proof.
  intros.
  rewrite fmap_comp.
  reflexivity.
Qed.

Class CompFunctor (f : forall A : Type, Comp A -> Type) : Type := {
  tmap : forall {a b : Type} {P : Comp a}
                (k : a -> b), f a P -> f b (fmap k P);

  tmap_id   : forall (a : Type) (P : Comp a) (x : f a P),
    tmap id x = rew <- @fmap_id_x Comp _ _ a P in x;
  tmap_comp : forall (a b c : Type) (P : Comp a)
                     (g : a -> b) (k : b -> c) (x : f a P),
    tmap k (tmap g x) =
    rew <- @fmap_comp_x Comp _ _ a b c k g P in tmap (k \o g) x
}.

(*
Instance Tainted_CompFunctor `{Functor m} : CompFunctor (Tainted m) := {
  tmap := fun A B P f x =>
    match x in Tainted _ _ P return Tainted m (fmap f P) with
      TT P action =>
        TT m (fmap f P) (fmap[m] (fun p => match p with
          | inl (exist x H) =>
            inl (exist _ (f x) (computes_map f x H))
          | inr x => inr (f x)
          end) action)
    end
}.
Proof.
  - intros.
    destruct x.
    
Abort.
*)

Instance Tainted_Functor `{Functor m} :
  Functor (fun A => { c : Comp A & Tainted m c }) := {
  fmap := fun _ B f x =>
    match x with
      existT P action =>
        existT (Tainted m (A:=B)) (fmap f P)
               (fmap (fun p =>
                        match p with
                        | inl (exist x H) =>
                          inl (exist _ (f x) _ (* (computes_map f x H) *))
                        | inr x => inr (f x)
                        end) action)
    end
}.
Proof.
  simpl.
  breakdown.
Defined.

Local Obligation Tactic := idtac.

Lemma existT_equal (A : Type) (P : A -> Type) (x y : A) (H : P x) (J : P y) :
  forall (Heqe : x = y), rew Heqe in H = J -> existT P x H = existT P y J.
Proof. intros; subst; f_equal. Qed.

Program Instance Tainted_FunctorLaws `{FunctorLaws m} :
  FunctorLaws (fun A => { c : Comp A & Tainted m c }).
Obligation 1.
  intros.
  extensionality x.
  destruct x.
  unfold fmap.
  unfold Tainted_Functor.
  pose proof (@fmap_id_x Comp _ _ a x) as Heqe.
  Require Import EqdepFacts.
  apply eq_sigT_iff_eq_dep.
  unfold Tainted in t.
  (* apply (eq_dep_intro _ _ _ _). *)
  (* apply eq_sigT_sig_eq. *)
  (* exists Heqe. *)
Admitted.
Obligation 2.
Admitted.