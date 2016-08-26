Section AST.

Inductive type : Type :=
  | Unit : type
  | Prod : type -> type -> type
  | Sum  : type -> type -> type
  | Func : type -> type -> type.

Variable var : type -> Type.

Inductive Pat : type -> Type :=
  | UnitPat : Pat Unit
  | VarPat  : forall t, var t -> Pat t
  | Pair    : forall a b, Pat a -> Pat b -> Pat (Prod a b).

Inductive term : type -> Type :=
  (* | TUnit : term Unit *)

  (* | TProd : forall a b, term a -> term b -> term (Prod a b) *)
  (* | TSumL : forall a b, term a -> term (Sum a b) *)
  (* | TSumR : forall a b, term b -> term (Sum a b) *)

  | TVar : forall t, var t -> term t
  | TAbs : forall dom cod, Pat dom -> term cod -> term (Func dom cod)
  | TApp : forall dom cod, term (Func dom cod) -> term dom -> term cod.

Inductive Morphism : type -> type -> Type :=
    (* Category *)
  | Id      : forall a, Morphism a a
  | Comp    : forall {a b c}, Morphism b c -> Morphism a b -> Morphism a c
    (* Cartesian *)
  | Exl     : forall {a b}, Morphism (Prod a b) a
  | Exr     : forall {a b}, Morphism (Prod a b) b
  | Eprod   : forall {a b c},
      Morphism a b -> Morphism a c -> Morphism a (Prod b c)
    (* Co-Cartesian *)
  | Inl     : forall {a b}, Morphism a (Sum a b)
  | Inr     : forall {a b}, Morphism b (Sum a b)
  | Esum    : forall {a b c},
      Morphism b a -> Morphism c a -> Morphism (Sum b c) a
    (* Closed *)
  | Apply   : forall {a b}, Morphism (Prod (Func a b) a) b
  | Curry   : forall {a b c}, Morphism (Prod a b) c -> Morphism a (Func b c)
  | Uncurry : forall {a b c}, Morphism a (Func b c) -> Morphism (Prod a b) c
    (* Primitives *)
  | Prim    : forall {a b}, (term a -> term b) -> Morphism a b
  | Const   : forall {a b},            term b  -> Morphism a b.

End AST.

Arguments UnitPat [var].
Arguments VarPat [var t] _.
Arguments Pair [var _ _] _ _.

(* Arguments TUnit [var]. *)

(* Arguments TProd [var _ _] _ _. *)
(* Arguments TSumL [var _ _] _. *)
(* Arguments TSumR [var _ _] _. *)

Arguments TVar [var t] _.
Arguments TAbs [var dom cod] _ _.
Arguments TApp [var dom cod] _ _.

Arguments Id      [var] a.
Arguments Comp    [var a b c] _ _.
Arguments Exl     [var a b].
Arguments Exr     [var a b].
Arguments Eprod   [var a b c] _ _.
Arguments Inl     [var a b].
Arguments Inr     [var a b].
Arguments Esum    [var a b c] _ _.
Arguments Apply   [var a b].
Arguments Curry   [var a b c] _.
Arguments Uncurry [var a b c] _.
Arguments Prim    [var a b] _.
Arguments Const   [var a b] _.

Section Denotation.

Require Import Coq.Program.Basics.

Fixpoint typeDenote (t : type) : Type :=
  match t with
  | Unit         => unit
  | Prod a b     => typeDenote a * typeDenote b
  | Sum a b      => typeDenote a + typeDenote b
  | Func arg ret => typeDenote arg -> typeDenote ret
  end.

Fixpoint termDenote {t : type} (e : term typeDenote t) : typeDenote t :=
  match e in term _ t0 return t = t0 -> typeDenote t0 with
  (* | TUnit      => fun _ => tt *)
  (* | TProd x y  => fun _ => (termDenote x, termDenote y) *)
  (* | TSumL x    => fun _ => inl (termDenote x) *)
  (* | TSumR x    => fun _ => inr (termDenote x) *)
  | TVar x     => fun _ => x
  | TAbs p f   => fun _ => fun _ => termDenote f
  | TApp e1 e2 => fun _ => termDenote e1 (termDenote e2)
  end eq_refl.

Fixpoint denote {a b} (m : Morphism typeDenote a b) : typeDenote (Func a b) :=
  match m with
  | Id a       => @id (typeDenote a)
  | Comp f g   => Basics.compose (denote f) (denote g)
  | Exl        => fst
  | Exr        => snd
  | Eprod f g  => fun x => (denote f x, denote g x)
  | Inl        => inl
  | Inr        => inr
  | Esum f g   => fun x => match x with
                           | inl y => denote f y
                           | inr y => denote g y
                           end
  | Apply      => fun p => fst p (snd p)
  | Curry f    => fun a b => denote f (a, b)
  | Uncurry f  => fun p => denote f (fst p) (snd p)
  | Prim f     => fun x => termDenote (f (TVar x))
  | Const x    => fun _ => termDenote x
  end.

Require Import Coq.Program.Equality.

Definition convertVar {var a b} (p : Pat var a) (u : var b)
  (eq_dec : forall t1 (x : var t1) t2 (y : var t2),
      {t1 = t2 /\ JMeq x y} + {~ JMeq x y}) :
  option (Morphism var a b).
Proof.
  induction p.
  - exact None.
  - destruct (eq_dec _ u _ v).
      destruct a; subst.
      exact (Some (Id _)).
    exact None.
  - destruct IHp2.
      exact (Some (Comp m Exr)).
    destruct IHp1.
      exact (Some (Comp m Exl)).
    exact None.
Defined.

Definition convert {var dom cod} (p : Pat var dom) (x : term var cod)
         (eq_dec : forall t1 (x : var t1) t2 (y : var t2),
             {t1 = t2 /\ JMeq x y} + {~ JMeq x y})
        (* (occurs : forall t, unit -> unit -> bool) *) :
  option (Morphism var dom cod) :=
  let fix go {dom cod} (p : Pat var dom) (x : term var cod) :=
  match p, x with
  | Pair p q, e        =>
    (* if negb (occurs q e) *)
    (* then Comp (convert p e) Exl *)
    (* else if negb (occurs p e) *)
    (* then Comp (convert q e) Exr *)
    (* else False_rect _ _ *) None
  | p, TVar v   => convertVar p v eq_dec
  | p, TAbs q e =>
    match go (Pair p q) e with
    | None => None
    | Some f => Some (Curry f)
    end
  | p, TApp u v =>
    match go p u with
      | None => None
      | Some pu =>
        match go p v with
        | None => None
        | Some pv =>
          Some (Comp Apply (Eprod pu pv))
        end
    end
  (* | _,         _        => None *)
  end in go p x.

End Denotation.

Bind Scope Morphism_scope with Morphism.

Delimit Scope Morphism_scope with CCC.

Infix "~>" := Morphism (right associativity, at level 52) : Morphism_scope.

Notation "^" := TVar (at level 49) : Morphism_scope.
Notation "\ x : t , e" := (TAbs (dom:=t) (VarPat (TVar x)) e)
  (no associativity, at level 100, x at level 0) : Morphism_scope.
Infix "@" := TApp (left associativity, at level 50) : Morphism_scope.

(* Notation "()" := TUnit (at level 49) : Morphism_scope. *)

Notation "[ e ]" := (fun _ => e) : Morphism_scope.

Definition Term t := forall v, term v t.

Definition eval {t} (e : Term t) : typeDenote t := termDenote (e typeDenote).

Compute ((fun x => eval [(\x : Unit, ^x) @ ^tt]) 0)%CCC.
