Require Import Eqdep.
Require Import FunctionalExtensionality.
Require Import Program.
Require Export List.
Require Import Morphisms Setoid Program Utf8.
(** Require Import ... *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.
Set Asymmetric Patterns.

Notation "f $ x"  := (f x) (right associativity, at level 35, only parsing).
Reserved Notation "f <$> x"  (at level 51, right associativity).
Reserved Notation "f <*> x"  (at level 51, right associativity).
Reserved Notation "x >>= f"  (at level 50, left associativity).
Reserved Notation "x >> y"   (at level 70, right associativity).
(** Tactics and HintDBs. *)
Create HintDb mohints.
Create HintDb mohints'.

Hint Extern 1 (_ /\ _) => repeat split.

Ltac equality := intuition congruence.

Ltac cases H := ((is_var H; destruct H) 
              || match type of H with
                 | {_} + {_} => destruct H
                 | _         => let Heq := fresh "Heq" in destruct H eqn:Heq
                 end); repeat (match goal with
                       | [ H' : _ = left _ |- _ ]  => clear H'
                       | [ H' : _ = right _ |- _ ] => clear H'
                       end).

Ltac mauto   := repeat (match goal with
	                     | [ H0 : ?P |- ?P ]               => exact H0
	                     | [ |- True ]                     => constructor
	                     | [ |- _ /\ _ ]                   => constructor
	                     | [ |- _ -> _ ]                   => intro
	                     | [ H0 : False |- _ ]             => cases H0
	                     | [ H0 : _ /\ _ |- _ ]            => cases H0
	                     | [ H0 : _ \/ _ |- _ ]            => cases H0
	                     | [ H0 : ?P -> ?Q, H1 : ?P |- _ ] => specialize (H0 H1)
	                     end).
	                     
Ltac rewrite_unfold  := mauto; 
                        cbn; 
                        (repeat (autorewrite with mohints + autounfold with mohints')); 
                        try congruence.
(** end *)

Hint Unfold compose : mohints mohints'.

Ltac aux_match_maker v := match v with
    | context [match ?w with _ => _ end] => aux_match_maker w
    | _ => destruct v
    end.

Ltac match_maker := match goal with
                    | |- context [match ?v with _ => _ end] => aux_match_maker v
                    end.

Ltac solve_lambda :=
      rewrite_unfold; f_equal;
      match goal with 
      | |- (fun _ => _) = _ => let var := fresh "var" in extensionality var
      | |- _ = (fun _ => _) => let var := fresh "var" in extensionality var
      | _                   => idtac
      end; rewrite_unfold.

Obligation Tactic := rewrite_unfold.

(** Functors *)
 
Class Functor (F : Type -> Type) : Type := {
    fmap     `{a : Type} `{b : Type} : (a -> b)  -> F a -> F b;
    fmap_id:       forall {a : Type} (x : F a),
                    fmap (@id a) x    = x;
    fmap_compose : forall {a b c : Type} (f : a -> b) (g : b -> c),
                    compose (fmap g) (fmap f) = fmap (compose g f);
 }.

Arguments fmap {F} {Functor} {a} {b} f x. 

(** Functors are proper morphisms : needed for rewrites *)
Add Parametric Morphism {a b} `{Functor F} : (@fmap F _ a b)
    with signature (pointwise_relation _ eq ==> eq ==> eq)
      as functor_morphism.
Proof.
         intros;
         f_equal;
         eapply functional_extensionality;
         intro arg; trivial.
Qed.

Hint Rewrite @fmap_id @fmap_compose : mohints.

Theorem fmap__id `{funF : Functor F} : forall {a : Type},
    fmap (@id a) = (@id (F a)).
Proof. intros. solve_lambda. Qed.

Theorem fmap__fmap `{funF : Functor F} : forall {a b c : Type} 
                          (g : b -> c) (f : a -> b) (x : F a),
             fmap g (fmap f x) = fmap (compose g f) x.
Proof. intros; rewrite <- fmap_compose; auto. Qed. 

Hint Rewrite @fmap__fmap @fmap__id : mohints.


Section Containers.

  Section Extension.
  
  Variable Shape    : Type.
  Variable Position : Shape -> Type.

  Inductive Ext (A : Type) : Type :=
  | ext: forall (s : Shape)
                (p : Position s -> A), Ext A.

  Global Arguments ext {A} s p.

    Definition shape {A : Type} (x : Ext A) : Shape :=
    match x with
      | ext s pf => s
    end.

  Definition position {A : Type} (x : Ext A) : Position (shape x) -> A :=
    match x with
      | ext s pf => pf
    end.

  Definition cfmap {a b : Type}
                  (f : a -> b)
                  (x : Ext a) : Ext b :=
    match x with
    | ext s p => ext s (fun x => f (p x))
    end.

  Arguments cfmap {a b} _ _.

  Global Program Instance ExtFunctor : Functor Ext := {
         fmap := @cfmap;
  }.
  Next Obligation.
    destruct x; unfold cfmap. auto.
  Defined.
  Next Obligation.
    solve_lambda.
    destruct var.
    solve_lambda.
  Defined.  
  End Extension.
  
  Hint Unfold cfmap : mohints.
  
  Lemma cfmap_compose {Shape : Type} {Position : Shape -> Type} {a b c : Type}
        (f : a -> b)
        (g : b -> c) :
        compose (@cfmap Shape Position b c g) (@cfmap Shape Position a b f) = cfmap (compose g f).
  Proof.
    solve_lambda;
    destruct var;
    solve_lambda.
  Qed.

  Lemma cfmap_id {Shape : Type} {Position : Shape -> Type} {a : Type} (x : Ext Position a) :
    cfmap id x = x.
  Proof.
    destruct x; unfold cfmap; auto.
  Qed.

  Hint Rewrite @cfmap_id @cfmap_compose : mohints mohints'.

  Section ContainerClass.
    
    Class Container (C : Type -> Type) := {
    Shape    : Type;
    Position : Shape -> Type;                 
    to       : forall {a : Type}, Ext Position a -> C a;
    from     : forall {a : Type}, C a -> Ext Position a;
    toFrom   : forall {a : Type} (a : C a),             to (from a) = a;
    fromTo   : forall {a : Type} (e : Ext Position a),  from (to e) = e
                                       }.

  End ContainerClass.

  Context `{Container C}.
  Definition container_fmap := fun {a b : Type}
                  (f : a -> b)
                  (x : C a) =>
    to (@cfmap Shape Position a b f (from x)).

  Lemma container_fmap_id {A : Type} (a : C A) :
    container_fmap id a = a.
  Proof.
    unfold container_fmap.
    rewrite cfmap_id.
    rewrite toFrom.
    reflexivity.
  Qed.

  Lemma container_fmap_compose {a b c : Type}
        (f : a -> b)
        (g : b -> c) :
        compose (container_fmap g) (container_fmap f) = container_fmap (compose g f).
  Proof.
    unfold container_fmap.
    rewrite <- cfmap_compose.
    unfold compose.
    extensionality y.
    rewrite fromTo.
    auto.
  Qed.
  
  Global Program Instance container : Functor C := {
         fmap := @container_fmap;
                                                         }.
  Next Obligation.  
    apply container_fmap_id.
  Defined.
  Next Obligation.
    apply container_fmap_compose.
  Defined.  
End Containers.

Coercion container : Container >-> Functor.
  
Class Applicative (F : Type -> Type) : Type := {
          functor :> Functor F;
          pure    `{a : Type}             :    a -> F a;
          ap      `{a : Type} `{b : Type} : F (a -> b) -> F a -> F b;
          ap_identity `{a : Type} : 
                        ap (pure (@id a)) = id;
          ap_composition: forall {a b c : Type}
                                 (v : F (a -> b))
                                 (u : F (b -> c)) (w : F a),
                ap (ap (ap (pure (fun f g x => f (g x))) u) v) w = ap u (ap v w);
          ap_homomorphism : forall {a b : Type}
                                   (x : a)
                                   (f : a -> b),
                ap (pure f)  (pure x) = pure (f x);
          ap_interchange : forall {a b : Type}
                                  (x : a)
                                  (u : F (a -> b)),
                ap u (pure x) = ap (pure (fun f => f x)) u;
          ap_fmap : forall {a b : Type}
                           (f : a -> b)
                           (x : F a),
                ap (pure f) x = fmap f x;
}.

Arguments pure {F Applicative a} _.
Arguments ap   {F Applicative a b} _ x.

Coercion functor : Applicative >-> Functor.

Infix "<*>" := ap.

Hint Rewrite @ap_composition @ap_homomorphism @ap_identity @ap_fmap : mohints.
Hint Rewrite <- @ap_interchange : mohints.

Theorem ap__identity `{AppF : Applicative F} `{a : Type} :
  forall (x : F a), ap (pure id) x = x.
Proof. intros; rewrite_unfold. Qed.

Theorem pure_fmap_pure `{AppF : Applicative F} :
  forall {a b : Type} (f : a -> b) (x : a), pure (f x) = fmap f (pure x).
Proof. intros;  rewrite <- ap_fmap, ap_homomorphism; auto. Qed.

Hint Rewrite @pure_fmap_pure @ap__identity : mohints. 

Class Monad (m : Type -> Type) : Type := {
          applicative :> Applicative m;
          
          ret   `{a : Type}   :               a -> m a;
          bind  `{a : Type} `{b : Type} :   m a -> (a -> m b) -> m b;
          
          right_unit: forall {a : Type} (x : m a), 
                           bind x (@ret a) = x;
          left_unit:  forall {a b:  Type} (x: a) (f : a -> m b),
                           bind (ret x) f = f x;
          associativity: forall {a b c: Type} (x: m a) (f: a -> m b) (g: b -> m c),
                            bind (bind x f) g = bind x (fun v : a => (bind (f v) g));
          fmap_monad: forall {a b: Type} (f : a -> b) (x : m a), 
                          fmap f x = bind x (fun y : a => ret (f y));
          pure_monad:   forall {a : Type},
                          (@pure m (@applicative) a) = (@ret a);
}.

Arguments ret  {m Monad a} _.
Arguments bind {m Monad a b} _ _.

Coercion applicative : Monad >-> Applicative.

Notation "x >>= f" := (bind x f).
Notation "x >> y"  := (x >>= fun _ => y).

Hint Rewrite @right_unit @left_unit @associativity @fmap_monad @pure_monad: mohints.

Theorem fmap_bind_right `{mm : Monad m} :
  forall (a b c : Type) (x : m a) (f : a -> m b) (g : b -> c),
             fmap g (x >>= f) = x >>= (fun y : a => fmap g (f y)).
Proof. intros; solve_lambda. Qed.

Theorem fmap_right_bind `{mm : Monad m} :
  forall (a b c : Type) (f : a -> b) (x : m a) (g : b -> m c),
      fmap f x >>= g = x >>= (fun y : a => g (f y)).
Proof. intros; solve_lambda. Qed.

Hint Rewrite @fmap_bind_right @fmap_right_bind : mohints.

Theorem fmap_bind_pure `{mm : Monad m} :
  forall (a b : Type) (f : a -> b) (x : m a),
      fmap f x = x >>= (fun y : a => pure (f y)).
Proof. intros; solve_lambda. Qed.

Theorem  ap_pure_bind `{mm : Monad m} :
  forall (a b : Type) (f : (a -> b)) (x : m a),
        ap (pure f) x = (pure f) >>= (fun g => x >>= (fun y => pure (g y))).
Proof. intros. rewrite ap_fmap. solve_lambda. Qed.

Hint Rewrite @fmap_bind_pure @ap_pure_bind : mohints.

(** Monad Instances *)

(*** Identity ***)

Section IdentityMonad.
  
Definition Identity (a : Type) : Type := a.

Global Program Instance IdentityFunctor : Functor Identity := {
   fmap := fun a b (f : a -> b) (x : a) => f x
}.
  Next Obligation.
    extensionality x; auto.
  Defined.
  
Global Program Instance IdentityApplicative : Applicative Identity := {
    functor := IdentityFunctor;
    pure    := fun {a : Type} (x : a) => x;
    ap      := fun {a : Type} {b: Type} (f : Identity a -> Identity b) (x : Identity a) => f x;
}.

Global Program Instance IdentityMonad : Monad Identity := {
   applicative := IdentityApplicative;
   ret         := fun {a : Type} (x : a) => x;
   bind        := fun {a : Type} {b : Type} (x : Identity a) (f : a -> Identity b) => f x;
}.                            

End IdentityMonad.

(*** State ***)

Definition State (st act : Type) := st -> (act * st)%type.

Section StateMonad.
Context `{s : Type}.

Global Program Instance StateFunctor : Functor (State s) := {
      fmap := fun a b => 
                  fun (f : a -> b) (x : State s a) => 
                      fun (st : s) => let (y, st') := x st in (f y, st');
}.
Obligation 1.
extensionality st; destruct (x st);  auto.
Defined.
Obligation 2.
    unfold compose.  
    extensionality x; extensionality st.
    destruct (x st).
    congruence.
Defined.

Global Program Instance StateApplicative : Applicative (State s) := {
    functor := StateFunctor;
    pure    := fun _ x     => fun st => (x, st);
    ap      := fun _ _ f x => fun st => let (f', st') := f st in
                                                              let (x', st'') := x st' in
                                                                   (f' x', st'');
}.
Obligation 1.
 intros; extensionality x; extensionality st; destruct (x st); auto. 
Defined.
Obligation 2.
intros; extensionality st; destruct (u st) as [r st']; destruct (v st') as [q st''];  destruct (w st'') as [j st''']; auto.
Defined.

Global Program Instance StateMonad : Monad (State s) := {
   applicative := StateApplicative;
   ret  := fun a (x : a) (st : s)    => (x, st);
   bind := fun a b (x : State s a)
              (f : a -> State s b) =>
                       fun (st : s)   => match x st with 
                                                  | (x', st')  => f x' st'
                                                  end
}.
Next Obligation.
  intros; extensionality st; destruct (x st); auto.
Defined.
Next Obligation.
  auto.
Defined.
Next Obligation.
  intros; extensionality st; destruct (x st); auto.
Defined.
Next Obligation.
  intros; extensionality st; destruct (x st); auto.
Defined.  
End StateMonad.

(** Monad Transformers *)
Class MonadTransformer (t : (Type -> Type) -> Type -> Type) : Type := {
    monad :> forall (m : Type -> Type), (Monad m) -> (Monad (t m));
    lift `{m : Type -> Type} `{mm : Monad m} `{tm: Monad (t m)} `{a : Type} : m a -> t m a;
    lift_return : forall {m : Type -> Type} {mm : Monad m}
                         (a : Type) (x : a),
                         lift (ret x) = ret x;
    lift_bind   : forall {m : Type -> Type} {mm : Monad m}
                         (a b : Type) (f : a -> m b) (x : m a),
                         lift (x >>= f) = (lift x) >>= (fun y : a => lift (f y));
 }.


Arguments lift {t MonadTransformer m mm tm a} _.

Hint Rewrite @lift_return @lift_bind : mohints.

(******************************************************************************)
(* Free monad transformer *)

Section FreeF.
    
  Inductive FreeF `(FuncF : Functor F) a x :=
  | pureF : a   -> FreeF FuncF a x
  | freeF : F x -> FreeF FuncF a x.

  Inductive FreeT `(FuncF : Functor F) `(Mo : Monad m) (a : Type) :=
  | freeT : forall x, (x -> (FreeT FuncF Mo a)) ->  m (FreeF FuncF a x) -> FreeT FuncF Mo a.
  
End FreeF.  

Section FreeC.
  Context `{Shape    : Type}.
  Context `{Position : Shape -> Type}.
  
  Inductive FreeC `(ConF : Container F) a :=
  | Pure : a -> FreeC ConF a
  | Free : Ext Position (FreeC ConF a) -> FreeC ConF a.

  Inductive FreeT2 `(ConF : Container F) (m : Type -> Type) (a : Type) :=
  | freeT2 : (FreeC ConF (FreeT2 ConF m a)) -> FreeT2 ConF m a.

End FreeC.



