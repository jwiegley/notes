Require Import Coq.Program.Program.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.JMeq.
Require Import Coq.omega.Omega.
Require Export Hask.Control.Monad.

Import ListNotations.

Generalizable All Variables.
(* Set Primitive Projections. *)
(* Set Universe Polymorphism. *)
(* Unset Transparent Obligations. *)

Inductive UnionF (a : Type) : list (Type -> Type) -> Type :=
  | UThis : forall t r, t a -> UnionF a (t :: r)
  | UThat : forall t r, UnionF a r -> UnionF a (t :: r).

Arguments UThis {a t r} _.
Arguments UThat {a t r} _.

Definition Union (r : list (Type -> Type)) (a : Type) := UnionF a r.

Lemma Union_empty : forall a, Union [] a -> False.
Proof. inversion 1. Qed.

(* A notation for natural transformations. *)
Notation "f ~> g" := (forall x, f x -> g x) (at level 90).

Definition Pos (t : Type -> Type) (r : list (Type -> Type)) := nat.

Inductive FindElem (t : Type -> Type) : list (Type -> Type) -> Type :=
  | Here : forall xs, FindElem t (t :: xs)
  | Next : forall t' xs, FindElem t xs -> FindElem t (t' :: xs).

Class Member (t : Type -> Type) (r : list (Type -> Type)) := {
  inj : forall v, t v -> Union r v;
  prj : forall v, Union r v -> option (t v);
  hasElem : FindElem t r
}.

Arguments inj {t r _ v} _.
Arguments prj {t r _ v} _.

Program Instance Member_Here (t : Type -> Type) (r : list (Type -> Type)) :
  Member t (t :: r) | 1 := {
  inj := fun _ x => UThis x;
  prj := fun _ x => _;
  hasElem := Here _ _
}.
Next Obligation.
  inversion x; subst; clear x.
    exact (Some X).
  exact None.
Defined.

Program Instance Member_Next (t t' : Type -> Type) (r : list (Type -> Type)) :
  Member t r -> Member t (t' :: r) | 2 := {
  inj := fun _ x => UThat (inj x);
  prj := fun _ x => _
}.
Next Obligation.
  inversion x; subst; clear x.
    exact None.
  exact (prj X).
Defined.
Next Obligation.
  apply Next, hasElem.
Defined.

Program Definition decomp `(u : Union (t :: r) v) : t v + Union r v :=
  match u in UnionF _ xs return (t :: r)%list = xs -> t v + Union r v with
  | UThis x => fun _ => inl (_ x)
  | UThat x => fun _ => inr x
  end eq_refl.

Program Definition extract `(u : Union [t] v) : t v :=
  match u in UnionF _ xs return [t] = xs -> t v with
  | UThis x => fun _ => _ x
  | UThat x => fun H => !
  end eq_refl.
Next Obligation. inversion x. Qed.

Definition weaken {t} `(u : Union r v) : Union (t :: r) v := UThat u.

Inductive Freer (f : Type -> Type) (a : Type) : Type :=
  | Pure : a -> Freer f a
  | Impure : forall x, f x -> (x -> Freer f a) -> Freer f a.

Arguments Pure {f a} _.
Arguments Impure {f a x} _ _.

Fixpoint Freer_map {r} `(f : a -> b) (x : Freer r a) : Freer r b :=
  match x with
  | Pure v => Pure (f v)
  | Impure u k => Impure u (fun x => Freer_map f (k x))
  end.

Program Instance Freer_Functor (f : Type -> Type) : Functor (Freer f) := {
  fmap := @Freer_map _
}.

Fixpoint Freer_ap {r} `(f : Freer r (a -> b)) (x : Freer r a) : Freer r b :=
  match f, x with
  | Pure f, Pure v     => Pure (f v)
  | Pure f, Impure u k => Impure u (fun x => Freer_map f (k x))
  | Impure u k, m      => Impure u (fun x => Freer_ap (k x) m)
  end.

Program Instance Freer_Applicative (f : Type -> Type) : Applicative (Freer f) := {
  pure := fun _ => Pure;
  ap := fun _ _ => Freer_ap
}.

Fixpoint Freer_join {r} `(f : Freer r (Freer r a)) : Freer r a :=
  match f with
  | Pure v     => v
  | Impure u k => Impure u (fun x => Freer_join (k x))
  end.

Program Instance Freer_Monad (f : Type -> Type) : Monad (Freer f) := {
  join := @Freer_join _
}.

Module FreerLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Program Instance Freer_FunctorLaws (f : Type -> Type) : FunctorLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold id.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold comp.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.

Program Instance Freer_ApplicativeLaws (f : Type -> Type) : ApplicativeLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  specialize (H y).
  destruct (f1 y); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction w, u, v; simpl; auto.
Admitted.                       (* exercise for the reader! ;) *)
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction u; auto.
  f_equal.
  extensionality x0.
  specialize (H x0).
  destruct (f1 x0); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  extensionality x0.
  destruct x0; auto.
Qed.

Program Instance Freer_MonadLaws (f : Type -> Type) : MonadLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.

End FreerLaws.

Definition Comp (A : Type) := A -> Prop.

Program Instance Comp_Functor : Functor Comp := {
  fmap := fun A B f (x : Comp A) b => exists a : A, x a /\ f a = b
}.

Program Instance Comp_Applicative : Applicative Comp := {
  pure := fun _ x a => x = a;
  ap   := fun A B mf mx r => exists f x, mf f /\ mx x /\ f x = r
}.

Program Instance Comp_Alternative : Alternative Comp := {
  empty  := fun A _ => False;
  choose := fun A x y s => x s \/ y s (* jww (2016-01-28): right? *)
}.

Program Instance Comp_Monad : Monad Comp := {
  join := fun A m r => exists t : Comp A, t r /\ m t
}.

Module CompLaws.

Import MonadLaws.

Require Import FunctionalExtensionality.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Ltac shatter :=
  unfold comp, id in *;
  repeat
    match goal with
    | [ H : _ = _           |- _               ] => subst
    | [ H : and _ _         |- _               ] => destruct H
    | [ H : exists _ : _, _ |- _               ] => destruct H
    | [                     |- exists _ : _, _ ] => eexists
    | [                     |- and _ _         ] => split
    end;
  simpl in *.

Ltac simplify_comp :=
  repeat let x := fresh "x" in extensionality x;
  try (apply prop_ext; split; intros);
  repeat (simpl; shatter; try constructor; eauto).

Local Obligation Tactic := simpl; intros; simplify_comp.

Program Instance Comp_FunctorLaws     : FunctorLaws Comp.
Program Instance Comp_ApplicativeLaws : ApplicativeLaws Comp.
Program Instance Comp_MonadLaws       : MonadLaws Comp.

End CompLaws.

Fixpoint injF `{Member eff r} `(f : Freer eff a) : Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure f k => Impure (inj f) (fun x => injF (k x))
  end.

Polymorphic Inductive Reader (e : Type) : Type -> Type := Ask : Reader e e.

Arguments Ask {e}.

Definition ask {e : Type} : Freer (Reader e) e :=
  Impure Ask Pure.

Fixpoint runReader `(x : e) `(f : Freer (Reader e) a) : a :=
  match f with
  | Pure v => v
  | Impure Ask k => runReader x (k x)
  end.

Inductive Writer (o : Type) : Type -> Type :=
  | Tell : o -> Writer o unit.

Arguments Tell {o} _.

Definition sendF `(t : f a) : Freer f a := Impure t Pure.

Definition tell `(x : o) : Freer (Writer o) unit := sendF (Tell x).

Fixpoint runWriter `(f : Freer (Writer o) a) : (list o * a) :=
  match f with
  | Pure v => (nil, v)
  | Impure (Tell x) k =>
      let '(l, v) := runWriter (k tt) in (x::l, v)%list
  end.

Program Fixpoint runReaderC `(x : e) `(f : Freer (Union (Reader e :: r)) a) : Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure u k =>
    match decomp u with
    | inl f => runReaderC x (k _)
    | inr u => Impure u (fun y => runReaderC x (k y))
    end
  end.
Next Obligation.
  destruct f.
  exact x.
Defined.

Definition runFreer (T : Type -> Type) `(f : Freer (Union (eff :: r)) a)
           (eta : a -> T a)
           (bind : forall t, eff t -> (t * T a))  :
  Freer (Union r) (T a).
Proof.
  induction f as [v|t u' k IHf].
    exact (Pure (eta v)).
  inversion u'; subst; clear u'.
    exact (let '(t, _) := bind _ X in IHf t).
  exact (Impure X IHf).
Defined.

(* Definition runReaderC' `(x : e) `(f : Freer (Union (Reader e :: r)) a) := *)
(*   runFreer id f (fun _ 'Ask => x). *)

(* Program Fixpoint runWriterC `(f : Freer (Union (Writer o :: r)) a) := *)
(*   runFreer (fun a => list o * a)%type f (fun _ '(Tell x) => tt) _. *)

Program Fixpoint runWriterC `(f : Freer (Union (Writer o :: r)) a) :
  Freer (Union r) (list o * a) :=
  match f with
  | Pure v => Pure (nil, v)
  | Impure u k =>
    match decomp u with
    | inl f =>
      res <- runWriterC (k _) ;
      let '(l, v) := res in
      pure (_ :: l, v)%list
    | inr u => Impure u (fun x => runWriterC (k x))
    end
  end.
Next Obligation.
  destruct f.
  exact o0.
Defined.
Next Obligation.
  destruct f.
  exact tt.
Defined.

Program Fixpoint runGetPut {e : Type} (x : e)
        `(f : Freer (Union (Reader e :: Writer e :: r)%list) a) :
  Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure u k =>
    match decomp u with
    | inl f => runGetPut x (k _)
    | inr u =>
      match decomp u with
      | inl f => runGetPut x (k _)
      | inr u => Impure u (fun y => runGetPut x (k y))
      end
    end
  end.
Next Obligation.
  destruct f.
  exact x.
Defined.
Next Obligation.
  destruct f.
  exact tt.
Defined.

Polymorphic Inductive State (s : Type) : Type -> Type :=
  | Get : State s s
  | Put : s -> State s unit.

Arguments Get {s}.
Arguments Put {s} _.

Program Fixpoint runState {s : Type} (x : s)
        `(f : Freer (Union (State s :: r)%list) a) :
  Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure u k =>
    match decomp u with
    | inl f => runState x (k _)
    | inr u => Impure u (fun y => runState x (k y))
    end
  end.
Next Obligation.
  destruct f.
    exact x.
  exact tt.
Defined.

Inductive Choice (A : Type) : Type :=
  | Pick : forall (P : A -> Prop), Choice A.

Arguments Pick {A} P.

(*
Inductive FTCQueue (m : Type -> Type) : Type -> Type -> Type :=
  | Leaf : forall a b, (a -> m b) -> FTCQueue m a b
  | Node : forall a x b, FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b.

Arguments Leaf {m a b} _.
Arguments Node {m a x b} _ _.

Fixpoint FTCQueue_size `(q : FTCQueue m a b) : nat :=
  match q with
  | Leaf x => 1%nat
  | Node n1 n2 => FTCQueue_size n1 + FTCQueue_size n2
  end.

Definition tsingleton {a m b} : (a -> m b) -> FTCQueue m a b := Leaf.

Definition snoc `(t : FTCQueue m a x) `(r : x -> m b) : FTCQueue m a b:=
  Node t (Leaf r).

Infix "|>" := snoc (at level 50).

Definition append {m a x b} :
  FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b := Node.

Infix "><" := append (at level 50).

(* Left view deconstruction data structure. *)
Inductive ViewL (m : Type -> Type) (a b : Type) : Type :=
  | TOne  : (a -> m b) -> ViewL m a b
  | TCons : forall x, (a -> m x) -> FTCQueue m x b -> ViewL m a b.

Arguments TOne {m a b} _.
Arguments TCons {m a b x} _.

Infix ":|" := TCons (at level 50).

Fixpoint ViewL_size `(v : ViewL m a b) : nat :=
  match v with
  | TOne _ => 1%nat
  | TCons _ q => 1%nat + FTCQueue_size q
  end.

Fixpoint tviewl_work {m x y z} (t : FTCQueue m x y) (tr : FTCQueue m y z) :=
  match t in FTCQueue _ x' y' return x' = x -> y' = y -> _ with
  | Leaf r => fun H1 H2 =>
      r :| rew <- [fun x => FTCQueue _ x _] H2 in tr
  | Node tl1 tl2 => fun H1 H2 =>
      tviewl_work tl1 (Node tl2 (rew <- [fun x => FTCQueue _ x _] H2 in tr))
  end eq_refl eq_refl.

Definition tviewl `(q : FTCQueue m a b) : ViewL m a b :=
  match q with
  | Leaf r => TOne r
  | Node t1 t2 => tviewl_work t1 t2
  end.

Lemma ViewL_size_tviewl_work {m x y z} (t : FTCQueue m x y) (tr : FTCQueue m y z) :
  ViewL_size (tviewl_work t tr) = FTCQueue_size t + FTCQueue_size tr.
Proof.
  generalize dependent tr.
  induction t; simpl; intros;
  unfold eq_rect_r, eq_rect, eq_sym; auto.
  rewrite IHt1; simpl.
  now rewrite plus_assoc.
Qed.

Lemma FTCQueue_ViewL_size `(x : FTCQueue m a b) :
  ViewL_size (tviewl x) = FTCQueue_size x.
Proof.
  induction x; simpl; auto.
  now rewrite ViewL_size_tviewl_work.
Qed.
*)

Definition comp `(f : A -> Prop) : Comp A := f.

Definition Eff (effs : list (Type -> Type)) (a : Type) : Type :=
  Freer (Union effs) a.

Program Instance Functor_Eff {r} : Functor (Eff r) := Freer_Functor _.
Program Instance Applicative_Eff {r} : Applicative (Eff r) := Freer_Applicative _.
Program Instance Monad_Eff {r} : Monad (Eff r) := Freer_Monad _.

Definition send `{Member eff effs} `(t : eff a) : Eff effs a :=
  Impure (inj t) Pure.

Import EqNotations.

Program Fixpoint Eff_size `(q : Eff effs a)
        (P : forall eff r, FindElem eff effs -> eff r -> r) : nat :=
  match q with
  | Pure x => 0%nat
  | @Impure _ _ T u k =>
    match effs as xs return effs = xs -> _ with
    | nil => fun _ => !
    | cons _ _ => fun H =>
      match decomp (rew [fun x => Union x T] H in u) with
      | inl f => 1%nat + Eff_size (k (_ u)) P
      | inr u => 1%nat + Eff_size (k (_ u)) P
      end
    end eq_refl
  end.
Next Obligation. inversion u. Qed.
Next Obligation.
  eapply P; eauto.
  constructor.
Defined.
Next Obligation.
  clear -u0 P.
  induction u0.
    eapply P; eauto.
    constructor.
  eapply IHu0; eauto.
  intros.
  eapply P; eauto.
  now constructor.
Defined.

Program Definition run `(f : Eff nil a) : a :=
  match f with
  | Pure x => x
  | Impure u k => False_rect _ _
  end.
Next Obligation.
  (* there are no more choices: effects are not possible *)
  inversion u.
Qed.

Import ListNotations.

Program Fixpoint runM `{M : Monad} `(f : Eff [m] a) : m a :=
  match f with
  | Pure x => pure x
  | Impure u q =>
    let mb := extract u in
    mb >>= (runM \o q)          (* jww (2018-06-15): precedence bug! *)
  end.

(*
Inductive Eff (effs : list (Type -> Type)) (a : Type) : Type :=
  | Val : a -> Eff effs a
  | E : forall b, Union effs b -> FTCQueue (Eff effs) b a -> Eff effs a.

Arguments Val {effs a} _.
Arguments E {effs a b} _ _.

Fixpoint Eff_size `(q : Eff effs a) : nat :=
  match q with
  | Val x => 1%nat
  | E u q => 1%nat + FTCQueue_size q
  end.

Definition Arrs effs := FTCQueue (Eff effs).
Arguments Arrs effs /.

Definition Freer_to_Eff {effs a} : Freer (Union effs) a -> Eff effs a.
Proof.
  induction 1 as [x|? u k IHf].
    exact (Val x).
  exact (E u (Leaf IHf)).
Defined.
*)

(*
Definition Eff_to_Freer {effs a} : Eff effs a -> Freer (Union effs) a.
Proof.
  destruct 1 as [x|? u q].
    exact (Pure x).
  induction q as [?? f|??? n1 IHn1 n2 IHn2].
    refine (Impure u (_ f)); intros.
    destruct (x X).
      exact (Pure b0).
*)

(*
Program Instance Functor_Eff {r} : Functor (Eff r) := {
  fmap := fun _ _ f x =>
    match x with
    | Val x => Val (f x)
    | E u q => E u (q |> (Val \o f))
    end
}.

Program Instance Applicative_Eff {r} : Applicative (Eff r) := {
  pure := fun _ => Val;
  ap := fun _ _ mf mx =>
    match mf, mx with
    | Val f, Val x => Val (f x)
    | Val f, E u q => E u (q |> (Val \o f))
    | E u q, m     => E u (q |> (fun f => fmap f m))
    end
}.

Program Definition Eff_bind `(m : Eff effs a) `(k : a -> Eff effs b) : Eff effs b :=
  match m with
  | Val x => k x
  | E u q => E u (q |> k)
  end.
*)

(* Program Definition Eff_join `(f : Eff effs (Eff effs r)) : Eff effs r := *)
(*   match f with *)
(*   | Val x => x *)
(*   | E u q => E u (q |> id) *)
(*   end. *)

Definition Arr effs a b := a -> Eff effs b.
Arguments Arr effs a b /.

(*
Program Fixpoint qApp `(q' : Arrs effs a b) (x : a) {measure (FTCQueue_size q')} :
  Eff effs b :=
  match tviewl q' with
  | TOne k    => k x
  | TCons k t =>
    match k x with
    | Val y => qApp t y
    | E u q => E u (q >< t)
    end
  end.
Next Obligation.
  rewrite <- !FTCQueue_ViewL_size.
  rewrite <- Heq_anonymous0; simpl.
  rewrite FTCQueue_ViewL_size.
  omega.
Qed.

Definition qComp `(g : Arrs effs a b) `(h : Eff effs b -> Eff effs' c) :
  Arr effs' a c := fun x => h (qApp g x).

Lemma Eff_size_qComp `(g : Arrs effs a b) `(h : Eff effs b -> Eff effs' c) :
  forall x, Eff_size (qComp g h x) <= FTCQueue_size g.
Proof.
  unfold qComp.
  induction g; simpl.
Abort.
*)

Definition computes_to {A : Type} (ca : Comp A) (a : A) : Prop := ca a.

Notation "c ↝ v" := (computes_to c v) (at level 40).

(*
Lemma qApp_Leaf effs a b (k : a -> Eff effs b) v :
  qApp (Leaf k) v = k v.
Proof. now unfold qApp, qApp_func, Fix_sub. Qed.
*)

(*
Lemma qApp_Leaf effs a x b
      (n1 : FTCQueue (Eff effs) a x) (n2 : FTCQueue (Eff effs) x b) v :
  qApp (Node n1 n2) v = match tviewl n1 with
                        | Val y => qApp n2 y
                        | E u q => E u (q >< n2)
                        end.
Proof.
  now unfold qApp, qApp_func, Fix_sub.
Qed.
*)

(*
Lemma qApp_size `(q' : Arrs effs a b) (x : a) :
  forall x, Eff_size (qApp q' x) <= FTCQueue_size q'.
Proof.
  induction q'; simpl;
  unfold qApp, qApp_func, Fix_sub; simpl.
Abort.
*)

Fixpoint handleRelay {eff effs a b}
         (ret : a -> Eff effs b)
         (h : forall v, eff v -> Arr effs v b -> Eff effs b)
         (f : Eff (eff :: effs) a) :
  Eff effs b :=
  match f with
  | Pure x => ret x
  | Impure u q =>
    let k := handleRelay ret h \o q in
    match decomp u with
    | inl x => h _ x k
    | inr u => Impure u k
    end
  end.

Definition interpretWith {eff effs a}
           (h : forall v, eff v -> Arr effs v a -> Eff effs a) :
  Eff (eff :: effs) a -> Eff effs a := handleRelay Pure h.

Definition interpret `(handler : eff ~> Eff effs) :
  Eff (eff :: effs) ~> Eff effs :=
  fun _ => interpretWith (fun _ e f => handler _ e >>= f).

Fixpoint interpose' {eff effs a b}
         `{M : Member eff effs}
         (ret : a -> Eff effs b)
         (h : forall v, eff v -> Arr effs v b -> Eff effs b)
         (f : Eff effs a) : Eff effs b :=
  match f with
  | Pure x => ret x
  | Impure u q =>
    let k := interpose' ret h \o q in
    match @prj eff effs M _ u with
    | Some x => h _ x k
    | None   => Impure u k
    end
  end.

Definition interposeWith {eff effs a} `{Member eff effs}
           (h : forall v, eff v -> Arr effs v a -> Eff effs a) :
  Eff effs a -> Eff effs a := interpose' Pure h.

Definition interpose `{Member eff effs} `(handler : eff ~> Eff effs) :
  Eff effs ~> Eff effs :=
  fun _ => interposeWith (fun _ e f => handler _ e >>= f).

Definition subsume `{Member eff effs} : Eff (eff :: effs) ~> Eff effs :=
  interpret (fun _ => send).

(* A Choice "effect" may be refined so long as every value computable from the
   new choice was computable from the original choice. *)
Inductive refineChoice {a} : Choice a -> Choice a -> Prop :=
  RefineChoice : forall old new, (forall v, new ↝ v -> old ↝ v) ->
     refineChoice (Pick new) (Pick old).

Definition State_func `(x : State s a) : s -> (s * a) :=
  match x with
  | Get   => fun s => (s, s)
  | Put s => fun _ => (s, tt)
  end.

Definition refineState {s s' a} (AbsR : s -> s' -> Prop) :
  State s a -> State s' a -> Prop :=
  fun old new => forall s, exists s', AbsR s s' ->
    let ro := State_func old s  in
    let rn := State_func new s' in
    AbsR (fst ro) (fst rn) /\ snd ro = snd rn.

Program Fixpoint refineBase {s s' a} (AbsR : s -> s' -> Prop)
        (old : Eff [State s] a) (new : Eff [State s'] a) : Prop :=
  match old, new with
  | Pure x, Pure y => x = y

  | Pure x, Impure u k =>
    match decomp u with
    | inl f => exists s, x = _ (snd (State_func f s))
    | inr u' => False_rect _ (Union_empty _ u')
    end

  | Impure u k, Pure y =>
    match decomp u with
    | inl f  => exists s, _ (snd (State_func f s)) = y
    | inr u' => False_rect _ (Union_empty _ u')
    end

  | Impure xu xk, Impure yu yk =>
    match decomp xu, decomp yu with
    | inl f,   inl g   =>
      exists (old : s) (new : s'), AbsR old new ->
        let ro := State_func f old in
        let rn := State_func g new in
        AbsR (fst ro) (fst rn) /\ snd ro = _ (snd rn)
    | inl _,   inr yu' => False_rect _ (Union_empty _ yu')
    | inr xu', inl _   => False_rect _ (Union_empty _ xu')
    | inr xu', inr _   => False_rect _ (Union_empty _ xu')
    end
  end.
Next Obligation.
  destruct f, g; auto.
  exact tt.
Defined.

Program Fixpoint reduction {s a}
        (act : Eff [Choice; State s] a) (res : a) : Prop :=
  match act with
  | Pure x => x = res
  | Impure u k =>
    match decomp u with
    | inl (Pick P) => exists v, P v /\ reduction (k v) res
    | inr u' =>
      match decomp u' with
      | inl f => exists s, reduction (k (snd (State_func f s))) res
      | inr u' => False_rect _ (Union_empty _ u')
      end
    end
  end.

Example reduction_works :
  reduction (s:=nat) (send (Put 10) ;;
                      x <- send Get ;
                      y <- send (Pick (fun x => x < 10));
                      pure (x + y)) 15.
Proof.
  simpl.
  exists 0, 10, 5.
  omega.
Qed.

Program Fixpoint raise {e} `(f : Eff effs a) : Eff (e :: effs) a :=
  match f with
  | Pure x => Pure x
  | Impure u k => Impure (weaken u) (fun x => raise (k x))
  end.

Local Obligation Tactic :=
  program_simpl; try (eapply Union_empty; eauto).

Program Fixpoint refine {s s' a} (AbsR : s -> s' -> Prop)
        (n : nat)
        (old : Eff [Choice; State s] a)
        (new : Eff [Choice; State s'] a) : Prop :=
  match n with
  | O => False
  | S n' =>
    match old, new with
    | Pure x, Pure y => x = y

    | Pure x, Impure u k =>
      match decomp u with
      | inl (Pick P) => exists v, P v /\ refine AbsR n' old (k v)
      | inr u' =>
        match decomp u' with
        | inl f => exists s,
           refine AbsR n' old (k (_ (snd (State_func f s))))
        | inr u' => !
        end
      end

    | Impure u k, Pure y =>
      match decomp u with
      | inl (Pick P) => exists v, P v /\ refine AbsR n' (k v) new
      | inr u' =>
        match decomp u' with
        | inl f => exists s,
           refine AbsR n' (k (_ (snd (State_func f s)))) new
        | inr u' => !
        end
      end

    | Impure xu xk, Impure yu yk =>
      match decomp xu, decomp yu with
      | inl f, inl g => refineChoice f (_ g)

      | inl (Pick P), inr yu' =>
        match decomp yu' with
        | inl g => exists v s,
            P v /\ refine AbsR n' (xk v) (yk (_ (snd (State_func g s))))
        | inr u' => !
        end

      | inr xu', inl (Pick P) =>
        match decomp xu' with
        | inl f => exists v s,
            P v /\ refine AbsR n' (xk (_ (snd (State_func f s)))) (yk v)
        | inr u' => !
        end

      | inr xu', inr yu' =>
        match decomp xu', decomp yu' with
        | inl f, inl g => exists s s', AbsR s s' ->
           refine AbsR n' (xk (_ (snd (State_func f s))))
                          (yk (_ (snd (State_func g s'))))
        | inl _,   inr yu' => !
        | inr xu', inl _   => !
        | inr xu', inr _   => !
        end
      end
    end
  end.

Inductive choose {a r} : Eff (Choice :: r) a -> Eff r a -> Prop :=
  | PureChoice : forall x,
      choose (Pure x) (Pure x)
  | ImpureChoiceThis : forall A (P : A -> Prop) v k x,
      P v -> choose (k v) x ->
      choose (Impure (UThis (Pick P)) k) x
  | ImpureChoiceThat : forall u k v,
      choose (k v) (Impure u Pure) ->
      choose (Impure (UThat u) k) (Impure u Pure).
