Require Import
  Coq.Strings.Ascii
  Coq.Strings.String.

Generalizable All Variables.

Open Scope string_scope.
Open Scope list_scope.

Section Lisp.
  Variable var : Type.

  Inductive Expr :=
    | EVar : var -> Expr
    | Enil : Expr
    | Et : Expr
    | EInteger : nat -> Expr
    (* | EFloat : nat -> Expr *)
    | EChar : ascii -> Expr
    | EString : string -> Expr
    (* | EVector : nat -> Expr *)
    (* | EHashTable : nat -> Expr *)
    | ESubr : (var -> Expr) -> Expr
    | EError : string -> Expr
    | ESymbol : string -> Expr
    | EQuote : Expr -> Expr
    | ECons : Expr -> Expr -> Expr.
End Lisp.

Arguments EVar [var] _.
Arguments Enil [var].
Arguments Et [var].
Arguments EInteger [var] _.
Arguments EChar [var] _.
Arguments EString [var] _.
Arguments ESubr [var] _.
Arguments EError [var] _.
Arguments ESymbol [var] _.
Arguments EQuote [var] _.
Arguments ECons [var] _ _.

Definition Term := forall var, Expr var.

Notation "([ x ^ y ])" := (fun var => @ECons var x y).
Notation "# x" := (fun var => @ESymbol var x) (at level 100).

Definition nil : Term := fun var => @Enil var.

Notation "([ f ])" := (fun var => @ECons var f nil).
Notation "([ f , .. , x ])" :=
  (fun var => @ECons var (f var) .. (@ECons var (x var) (nil var)) ..)
  (right associativity).

Definition str (s : string) := fun var => @EString var s.
Definition num (n : nat)    := fun var => @EInteger var n.
Definition quote' (x : Term) := fun var => @EQuote var (x var).

Definition Flength var (e : Expr var) : Expr var :=
  let fix go e :=
    match e with
    | EVar x     => EVar x
    | Enil       => EInteger 0
    | Et         => EError "wrong-type-argument"
    | EInteger x => EError "wrong-type-argument"
    | EChar x    => EError "wrong-type-argument"
    | EString x  => EError "wrong-type-argument"
    | ESubr x    => EError "wrong-type-argument"
    | EError x   => EError x
    | ESymbol _  => EError "wrong-type-argument"
    | EQuote _   => EError "wrong-type-argument"
    | ECons a d  =>
      match go d with
      | EInteger n => EInteger (S n)
      | x => x
      end
    end in
  go e.

Compute Flength nat (([ num 10 , num 20 , num 30 ]) nat).

Fixpoint squash {var} (e : Expr (Expr var)) : Expr var :=
  let fix go e :=
    match e with
    | EVar x     => x
    | Enil       => Enil
    | Et         => Et
    | EInteger x => EInteger x
    | EChar x    => EChar x
    | EString x  => EString x
    | ESubr f    => ESubr (fun x => squash (f (EVar x)))
    | EError x   => EError x
    | ESymbol _  => EError "wrong-type-argument"
    | EQuote x   => EQuote (squash x)
    | ECons a d  => ECons (squash a) (squash d)
    end in
  go e.

Definition subr (f : forall var, Expr var -> Expr var) :=
  fun var => @ESubr var (fun v => f var (EVar v)).

Check ([ #"message" , str "Hello, world!" , ([ subr Flength , num 10 ]) ]).

Fixpoint ident {var} (e : Expr var) : Expr var :=
  match e with
  | EVar x     => EVar x
  | Enil       => Enil
  | Et         => Et
  | EInteger x => EInteger x
  | EChar x    => EChar x
  | EString x  => EString x
  | ESubr k    => ESubr (fun x => ident (k x))
  | EError x   => EError x
  | ESymbol s  => ESymbol s
  | EQuote x   => EQuote (ident x)
  | ECons a d  => ECons (ident a) (ident d)
  end.

Fixpoint eval (e : Term) : Term := fun var =>
  let fix go (e : Expr var) :=
    match e with
    | EVar x     => EVar x
    | Enil       => Enil
    | Et         => Et
    | EInteger x => EInteger x
    | EChar x    => EChar x
    | EString x  => EString x
    | ESubr k    => ESubr (fun v : var => go (k v))
    | EError x   => EError x
    | ESymbol s  => ESymbol s      (* need to lookup variable value *)
    | EQuote x   => x
    | ECons (ESubr f) x => go (f (go x))
    | ECons a d  => ECons (go a) (go d)
    end in
  go (e var).

(* (length . ((quote . ((1 . (2 . (3 . nil))))) . nil)) *)

Eval compute [subr quote'] in
    (([ subr (@Flength) ,
        quote' ([ num 10 , num 20 , num 30 ]) ]) nat).

Example ex_length_3 :
  eval (([ subr (@Flength) ,
           quote' ([ num 10 , num 20 , num 30 ]) ]) (Expr nat)) =
  num 3 nat.
Proof.
  unfold subr, squash.
  simpl.
  unfold num.
  reflexivity. Qed.