Require Import Fiat.ADT Fiat.ADTNotation Here.PipesFiat.

Program Definition Spec := Def ADT {
  rep := Producer nat unit,

  Def Constructor0 "empty" : rep :=
    ret (empty _ _),,

  Def Method1 "add" (r : rep) (n : nat) : rep * nat :=
    ret (forP r (fun x => yield (x + n)), n),

  Def Method0 "peel" (r : rep) : rep * option nat :=
    p <- next r;
    ret (match p with
         | inl x => (empty _ _, None)
         | inr (a, n) => (n, Some a)
         end)
}.

Open Scope string_scope.

Definition add (r : Rep Spec) (n : nat) : Comp (Rep Spec * nat) :=
  Eval simpl in let addS := "add" in callMeth Spec addS r n.

Inductive Term (c : Type) (a : Type) :=
  | Get   : (c -> Term c a) -> Term c a
  | Put   : c -> Term c a -> Term c a
  | Done  : a -> Term c a
  | Error : Term c a.

Arguments Get {c a} _.
Arguments Put {c a} _ _.
Arguments Done {c a} _.
Arguments Error {c a}.

Inductive transformed {c a : Type} :
  Comp (Producer c unit * a) -> Term c a -> Prop :=
  | TermGet   : forall (P : Comp c) k f,
      (* jww (2016-10-03): How do I relate [P] to a predicate on the value
         resulting from [Get]? *)
      (forall v, P v -> transformed (k v) (f v))
        -> transformed (z <- P; k z) (Get f)
  | TermPut   : forall ca s r, transformed ca r -> transformed ca (Put s r)
  | TermDone  : forall r b k (v : b), transformed (ret (r, k v)) (Done (k v))
  | TermError : forall ca, transformed ca Error.

Hint Constructors transformed.

Definition addC (r : Rep Spec) (n : nat) : Comp (Rep Spec * nat) :=
  Eval simpl in let addS := "add" in callMeth Spec addS r n.

Ltac compileTerm :=
  repeat match goal with
  | [ |- transformed (_ <- { _ | _ }; _) _ ] => eapply TermGet
  | [ |- transformed (ret _) _ ] => eapply TermDone
  end; intros.

Lemma addT : { f : nat -> Term nat nat
             & forall r n, transformed (addC r n) (f n) }.
Proof.
  exists (fun n => Get (fun x => Put (x + n) (Done n))).
  unfold addC; intros.
  (* apply TermGet; intros. *)
  (* (* A [Put] can be inserted anywhere, since it is orthogonal to the semantics *)
  (*    of the computation. *) *)
  (* apply TermPut with (s:=20). *)
  (* apply TermDone. *)
Admitted.

Definition addT' := Eval simpl in projT1 addT.
Print addT'.
(* addT' = fun r : () => Get (fun v : nat => Put 20 (Done (r, v + 10))) *)
