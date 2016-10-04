Require Import Fiat.ADT Fiat.ADTNotation Here.PipesFiat.

Definition Stream (A : Type) := nat -> Comp A.

Definition nth_smallest `{StrictOrder A R} (n : nat) (s : Comp A) : Comp A :=
  { i | exists xs, (In _ s i <-> List.In i xs)
          /\ Sorted.Sorted R xs /\ i = List.nth n xs i }.

Definition map {A B} (f : A -> B -> Prop) (s : Stream A) : Stream B := fun n =>
  { b : B | exists a, s n a /\ f a b }.

Definition filter {A} (f : A -> Prop) (s : Stream A) : Stream A := fun n =>
  i <- nth_smallest n { i | exists x, s i x /\ f x };
  s i.

Definition flatten {A} (s : Stream (Stream A)) : Stream A := fun n =>
  `(i, j) <- nth_smallest n
     { p | forall i j : nat, p = (i, j) -> exists s' x, s i s' /\ s' j x };
  s' <- s i;
  s' j.

Definition bind {A B} (f : A -> Stream B -> Prop) (s : Stream A) : Stream B :=
  flatten (map f s).

Require Import Fiat.Computation.FixComp.
Import LeastFixedPointFun.

Definition foldr_spec `(f : B -> A -> A) (z : A) (s : Stream B) : Stream A :=
  LeastFixedPoint (fDom:=[nat : Type]%list)
    (fun rec pos =>
       b <- s pos;
       z' <- match pos with
             | O => ret z
             | S n => rec n
             end;
       ret (f b z')).

(* A pipe connects two bi-directional streams and produces a result after a
   number of steps. *)
Record Pipe (A' A B' B R : Type) := mkPipe {
  segment : (A' -> Stream A) -> (B -> Stream B') -> Comp R;
  proper  :
    Proper (pointwise_relation A' (pointwise_relation nat refine) ==>
            pointwise_relation B  (pointwise_relation nat refine) ==>
            refine) segment
}.

Arguments Pipe A' A B' B R.

Definition refine_pipe `(x : Pipe A' A B' B R) (y : Pipe A' A B' B R) :=
  forall inc out, refine (segment x inc out) (segment y inc out).

Infix "=|" := refine_pipe (at level 100).

Notation "()" := (unit : Type).

Definition Void := False.

Definition Producer := Pipe Void () ().

Definition Producer' B R := forall {X' X}, Pipe X' X () B R.

Program Definition yield {X' X A} (x : A) : Pipe X' X () A () :=
  {| segment := fun _inc out => out x 0; proper := _ |}.
Obligation 1.
  intros ??????.
  rewrite H0.
  reflexivity.
Qed.

Program Definition forP `(p : Pipe x' x b' b a') `(f : b -> Pipe x' x c' c b') :
  Pipe x' x c' c a' :=
  {| segment :=
       fun inc out =>
         segment p inc
                 (fun b i =>
                    segment (f b) inc
                            (fun c j =>
                               n <- { n | exists s, nth_smallest n s (i, j) };
                                 out c n))
   ; proper := _ |}.
Obligation 1.
  intros ??????.
  destruct p; simpl.
  rewrite H.
  f_equiv.
  intros ??.
  destruct (f a); simpl.
  rewrite H.
  setoid_rewrite H0.
  reflexivity.
Qed.

Ltac compext :=
  apply Extensionality_Ensembles;
  split; intros; intros ??.

Definition Spec := Def ADT {
  rep := unit,

  Def Constructor0 "empty" : rep := ret tt,,

  Def Method0 "foo" (r : rep) : rep * nat :=
    n <- { n : nat | n < 100 };
    ret (r, n + 10)
}.

Open Scope string_scope.

Definition foo (r : Rep Spec) : Comp (Rep Spec * nat) :=
  Eval simpl in let fooS := "foo" in callMeth Spec fooS r.

Inductive Term (c : Type) (a : Type) :=
  | Get   : (c -> Term c a) -> Term c a
  | Put   : c -> Term c a -> Term c a
  | Done  : a -> Term c a
  | Error : Term c a.

Arguments Get {c a} _.
Arguments Put {c a} _ _.
Arguments Done {c a} _.
Arguments Error {c a}.

Inductive transformed {c a : Type} : Comp a -> Term c a -> Prop :=
  | TermGet   : forall (P : Comp c) k f,
      (* jww (2016-10-03): How do I relate [P] to a predicate on the value
         resulting from [Get]? *)
      (forall v, P v -> transformed (k v) (f v))
        -> transformed (z <- P; k z) (Get f)
  | TermPut   : forall ca s r, transformed ca r -> transformed ca (Put s r)
  | TermDone  : forall b k (v : b), transformed (ret (k v)) (Done (k v))
  | TermError : forall ca, transformed ca Error.

Hint Constructors transformed.

Definition fooC (r : Rep Spec) : Comp (Rep Spec * nat) :=
  Eval simpl in let fooS := "foo" in callMeth Spec fooS r.

Ltac compileTerm :=
  repeat match goal with
  | [ |- transformed (_ <- { _ | _ }; _) _ ] => eapply TermGet
  | [ |- transformed (ret _) _ ] => eapply TermDone
  end; intros.

Lemma fooT : { f : Rep Spec -> Term nat (Rep Spec * nat)
             & forall r, transformed (fooC r) (f r) }.
Proof.
  eexists.
  unfold fooC; intros.
  apply TermGet; intros.
  (* A [Put] can be inserted anywhere, since it is orthogonal to the semantics
     of the computation. *)
  apply TermPut with (s:=20).
  apply TermDone.
Defined.

Definition fooT' := Eval simpl in projT1 fooT.
Print fooT'.
(* fooT' = fun r : () => Get (fun v : nat => Put 20 (Done (r, v + 10))) *)
