Require Import
  Coq.Lists.List
  Coq.Strings.String
  Hask.Control.Monad.Free
  Fiat.Common.ilist
  FIDL.Tactics
  FIDL.Comp.

Generalizable All Variables.

Import ListNotations.

(*
Definition Effect := forall (x : Type), Type -> (x -> Type) -> Type.

Inductive EFFECT : Type :=
  MkEff : Type -> Effect -> EFFECT.

Inductive EffElem : Effect -> Type -> list EFFECT -> Type :=
  | Here a x xs : EffElem x a (MkEff a x :: xs)
  | There a x y xs : EffElem x a xs -> EffElem x a (y :: xs).

Arguments Here {a x xs}.
Arguments There {a x y xs} n.

Definition updateResTy `(val : t) (xs : list EFFECT)
  `(prf : EffElem e a xs) `(n : e t a b) : list EFFECT.
Proof.
  destruct xs.
    apply nil.
  destruct e0.
  match xs with
  | nil => fun _ _ => nil
  | x :: xs =>
    match x with
      MkEff 
    fun (x' : 
  | MkEff _ _ :: xs, Here _ _ _ => MkEff (b val) e :: xs
  | x :: xs, There _ _ _ _ p => x :: @updateResTy t val xs e a p n
  end.
    
updateResTy {b} val (MkEff a e :: xs) Here n = 
updateResTy     val (x :: xs)    (There p) n = 

updateResTy {b} val (MkEff a e :: xs) Here n = (MkEff (b val) e) :: xs
updateResTy     val (x :: xs)    (There p) n = x :: updateResTy val xs p n

Inductive EffM (m : Type -> Type) :
  forall (x : Type), list EFFECT -> (x -> list EFFECT) -> Type :=
  | Value x xs : forall `(val : x), EffM m (xs val) xs
  | EBind a b xs xs' (xs'' : b -> list EFFECT) : EffM m xs xs' ->
             (forall (val : a), EffM m (xs' val) xs'') -> EffM m xs xs''
  | CallP xs : forall (prf : List.In e xs ) (eff : e t a b),
             EffM m t xs (fun v => updateResTy v xs prf eff)

  | LiftP    : (prf : SubList ys xs) ->
             EffM m t ys ys' -> EffM m t xs (fun v => updateWith (ys' v) xs prf)

  | New      : Handler e' m ==> (e : EFFECT) -> resTy ->
             e = MkEff resTy e' ->
             EffM m t (e :: es) (fun v => e :: es) ->
             EffM m t es (fun v => es)

  | ECons  : (l : ty) ->
             EffM m t [x] xs' -> -- [x] (fun v => xs) ->
             EffM m t [l :: x] (fun v => map (cons l) (xs' v)).
*)