Require Import Coq.Bool.Bool.

Require Import Category.Lib.
Require Import Category.Theory.

Inductive type (ty : Type) : Type :=
  | Ty : ty -> type ty
  | Func : type ty -> type ty -> type ty.

Arguments Ty {ty} _.
Arguments Func {ty} _ _.

Inductive Lambda (kind : Type) (var : type kind -> Type)
          (s : (type kind -> Type) -> type kind -> Type) :
  type kind -> Type :=
  | V : forall t : type kind, var t -> Lambda kind var s t
  | Abs : forall d c : type kind,
      Lambda kind (fun t => var t + ())%type s c -> Lambda kind var s (Func d c)
  | App : forall d c : type kind,
      Lambda kind var s (Func d c) -> Lambda kind var s d -> Lambda kind var s c
  | Syn : forall t, s var t -> Lambda kind var s t
  (* | Let (var : Lambda) (body : @Lambda (var + ())) *).

Arguments V {kind var _ _} _.
Arguments Abs {kind var _ _ _} _.
Arguments App {kind var _ _ _} _ _.
Arguments Syn {kind var _ _} _.

Definition example1 :
  (* ∀ (f : () -> ()) (t : ()), f t : () *)
  Lambda () (fun _ => nat) (fun _ _ => False)
         (Func (Ty ()) (Func (Ty ()) (Ty ()))) :=
  Abs (Abs (App (d:=Ty ())
                (V (Datatypes.inl (Datatypes.inr ())))
                (V (Datatypes.inr ())))).

(* ∀ (x : obj_idx) (y : obj_idx) (f g : x ~> y), f ∘ g *)

Inductive kind : Set :=
  | Ob
  | Ar
  | Eqv.

Inductive entity (var : type kind -> Type) : kind -> Type :=
  | Obj : entity var Ob
  | Arr :
      Lambda kind (fun t => var t + ())%type
             (fun _ _ => False) (Ty Ob) ->
      Lambda kind (fun t => var t + ())%type
             (fun _ _ => False) (Ty Ob) -> entity var Ar.

Inductive term (var : type kind -> Type) : kind -> Type :=
  | Equiv :
      Lambda kind var (fun _ _ => False) (Ty Ar) ->
      Lambda kind var (fun _ _ => False) (Ty Ar) -> term var Eqv.

Arguments Obj {_}.
Arguments Arr {_} _ _.
Arguments Equiv {_} _ _.

Fixpoint entityD (t : type kind) : Type :=
  match t with
  | Ty x => nat
  | Func x x0 => entityD x -> entityD x0
  end.
Arguments entityD t /.

Definition example2 {var} :
  Lambda kind var (fun var t => term var Eqv)
         (Func (Ty Ob) (Func (Ty Ob) (Func (Ty Ar) (Func (Ty Ar) (Ty Eqv))))) :=
  Abs (Abs (Abs (Abs (Syn (Equiv (V (Datatypes.inr ()))
                                 (V (Datatypes.inl (Datatypes.inr ())))))))).

Require FunInd.

Fixpoint denote {t var} (e : Lambda kind entityD (fun var t => term var Eqv) t) :
  entityD t :=
  match e with
  | V x => x
  | @Abs _ _ _ d c x => fun y : entityD d => denote x
  | App x x0 => denote x (denote x0)
  | Syn (Equiv f g) => denote f ≈ denote g
  end.