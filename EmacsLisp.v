Require Import
  Coq.Strings.Ascii
  Coq.Strings.String.

Generalizable All Variables.

Open Scope string_scope.
Open Scope list_scope.

Section Lisp.
  Inductive type : Type :=
    | T : type
    | Nil : type
    | Integer : type
    | Char : type
    | String : type
    | Cons : type -> type -> type
    | Func : type -> type -> type
    | Symbol : type
    | Error : type.

  Inductive truth := TT.
  Inductive falsehood := NT.
  Record symbol := genSym { symbolId : string }.
  Record error := genError { errorMsg : string }.

  Variable var : type -> Type.

  Inductive term : type -> Type :=
    | TVar : forall t, var t -> term t
    | Tnil : term Nil
    | Tt : term T
    | TInteger : nat -> term Integer
    (* | TFloat : nat -> term *)
    | TChar : ascii -> term Char
    | TString : string -> term String
    (* | TVector : nat -> term *)
    (* | THashTable : nat -> term *)
    | TAbs : forall dom cod, (var dom -> term cod) -> term (Func dom cod)
    | TApp : forall dom cod, term (Func dom cod) -> term dom -> term cod
    | TError : string -> term Error
    | TSymbol : string -> term Symbol
    | TCons : forall a b, term a -> term b -> term (Cons a b).
End Lisp.

Arguments TVar [var t] _.
Arguments Tnil [var].
Arguments Tt [var].
Arguments TInteger [var] _.
Arguments TChar [var] _.
Arguments TString [var] _.
Arguments TAbs [var dom cod] _.
Arguments TApp [var dom cod] _ _.
Arguments TError [var] _.
Arguments TSymbol [var] _.
Arguments TCons [var _ _] _ _.

Definition Term t := forall var, term var t.

Notation "([ x ^ y ])" := (fun var => @TCons var x y).
Notation "# x" := (fun var => @TSymbol var x) (at level 100).

Definition nil : Term Nil := fun var => @Tnil var.

Notation "([ f ])" := (fun var => @TCons var f nil).
Notation "([ f , .. , x ])" :=
  (fun var => @TCons var (f var) .. (@TCons var (x var) (nil var)) ..)
  (right associativity).

Definition str (s : string) := fun var => @TString var s.
Definition num (n : nat)    := fun var => @TInteger var n.

Fixpoint Flength {var t} (e : term var t) : term var Error + term var Integer :=
  match e with
  | TVar _     => inl (TError "wrong-type-argument")
  | Tnil       => inr (TInteger 0)
  | Tt         => inl (TError "wrong-type-argument")
  | TInteger _ => inl (TError "wrong-type-argument")
  | TChar _    => inl (TError "wrong-type-argument")
  | TString _  => inl (TError "wrong-type-argument")
  | TAbs _     => inl (TError "wrong-type-argument")
  | TApp _ _   => inl (TError "wrong-type-argument")
  | TError x   => inl (TError x)
  | TSymbol _  => inl (TError "wrong-type-argument")
  | TCons _ d  => match Flength d with
                  | inr (TInteger n) => inr (TInteger (S n))
                  | _ => inl (TError "wrong-type-argument")
                  end
  end.

Fixpoint squash {var t} (e : term (term var) t) : term var t :=
  match e with
  | TVar x     => x
  | Tnil       => Tnil
  | Tt         => Tt
  | TInteger x => TInteger x
  | TChar x    => TChar x
  | TString x  => TString x
  | TAbs f     => TAbs (fun x => squash (f (TVar x)))
  | TApp e1 e2 => TApp (squash e1) (squash e2)
  | TError x   => TError x
  | TSymbol x  => TSymbol x
  | TCons a d  => TCons (squash a) (squash d)
  end.

(* Definition subr (f : forall var, term var -> term var) := *)
(*   fun var => @ESubr var (fun v => f var (EVar v)). *)

(* Check ([ #"message" , str "Hello, world!" , ([ subr Flength , num 10 ]) ]). *)

Fixpoint ident {var t} (e : term var t) : term var t :=
  match e with
  | TVar x     => TVar x
  | Tnil       => Tnil
  | Tt         => Tt
  | TInteger x => TInteger x
  | TChar x    => TChar x
  | TString x  => TString x
  | TAbs f     => TAbs (fun x => ident (f x))
  | TApp e1 e2 => TApp (ident e1) (ident e2)
  | TError x   => TError x
  | TSymbol s  => TSymbol s
  | TCons a d  => TCons (ident a) (ident d)
  end.

Fixpoint typeDenote (t : type) : Type :=
  match t with
  | T => truth
  | Nil => falsehood
  | Integer => nat
  | Char => ascii
  | String => string
  | Cons a d => (typeDenote a * typeDenote d)%type
  | Func arg ret => typeDenote arg -> typeDenote ret
  | Symbol => symbol
  | Error => error
  end.

Fixpoint termDenote {t} (e : term typeDenote t) : typeDenote t :=
  match e with
  | TVar x     => x
  | Tnil       => NT
  | Tt         => TT
  | TInteger x => x
  | TChar x    => x
  | TString x  => x
  | TAbs f     => fun v => termDenote (f v)
  | TApp e1 e2 => termDenote e1 (termDenote e2)
  | TError x   => genError x
  | TSymbol s  => genSym s
  | TCons a d  => (termDenote a, termDenote d)
  end.
