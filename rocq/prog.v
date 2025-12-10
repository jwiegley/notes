Require Import Coq.Program.Program.

Generalizable All Variables.

Set Universe Polymorphism.

Section prog.

Variable opT : Type -> Type.

Inductive prog : forall T:Type, Type :=
| BaseOp : forall T, opT T -> prog T
| Ret    : forall T, T -> prog T
| Bind   : forall T T', prog T -> (T -> prog T') -> prog T'.

Inductive Free (f : Type -> Type) (a : Type) : Type :=
| Pure : a -> Free f a
| Join : forall x, (x -> Free f a) -> f x -> Free f a.

Arguments Pure {f a} _.
Arguments Join {f a} _ _ _.

Fixpoint freeToProg `(fr : Free prog a) : prog a :=
  match fr with
    | Pure x => Ret _ x
    | Join _ g h => Bind _ _ h (freeToProg ∘ g)
  end.

Fixpoint progToFree `(fr : prog a) : Free prog a :=
  match fr with
    | BaseOp _ x   => Join _ Pure (BaseOp _ x)
    | Ret _ x      => Pure x
    | Bind _ _ h g => Join _ (progToFree ∘ g) h
  end.

Lemma freeToProg_progToFree_id `(x : prog T) :
  freeToProg (progToFree x) = x.
Proof.
  induction x; simpl; auto;
  unfold compose; simpl.
    (** jww (2017-07-26): I believe this is what makes this not a proper
        free monad.  Say you have:

          BaseOp T o >>= Ret

        The [Bind] constructor in this case, in order to match Free, must
        ignore the action of Ret. This could be the right behavior, but
        it requires interpreting the meaning of such an action, which a
        real Free structure would not do. *)
    assert (Bind _ _ (BaseOp T o) (Ret T) = BaseOp T o) by admit.
    apply H.
  f_equal.
  Require Import FunctionalExtensionality.
  extensionality x0.
  apply H.
Admitted.

Lemma progToFree_freeToProg_id `(x : Free prog T) :
  progToFree (freeToProg x) = x.
Proof.
  induction x; simpl; auto;
  unfold compose; simpl.
  f_equal.
  Require Import FunctionalExtensionality.
  extensionality x0.
  apply H.
Qed.

End prog.
