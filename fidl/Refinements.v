Require Import Fiat.ADT.

Lemma refine_match_ret :
  forall A B (xs : list B)  (a : A) (z : B -> list B -> A),
    refine (x0 <- match xs with
                  | nil => ret a
                  | cons x xs' => ret (z x xs')
                  end;
            ret x0)
           (ret (match xs with
                 | nil => a
                 | cons x xs' => (z x xs')
                 end)).
Proof.
  intros.
  induction xs; simpl;
  simplify with monad laws;
  reflexivity.
Qed.

Lemma refine_match_ret_pair :
  forall X Y Z (xs : list X) (x : Y) (y : Z)
               (z : X -> list X -> Y) (w : X -> list X -> Z),
    refine (x0 <- match xs with
                  | nil => ret (x, y)
                  | cons x xs' => ret (z x xs', w x xs')
                  end;
            ret (fst x0, snd x0))
           (ret (match xs with
                 | nil => (x, y)
                 | cons x xs' => (z x xs', w x xs')
                 end)).
Proof.
  intros.
  induction xs; simpl;
  simplify with monad laws;
  reflexivity.
Qed.

Lemma refine_pair A B (x : Comp (A * B)) :
  refine (v <- x; ret (fst v, snd v)) x.
Proof.
  eexists.
  destruct v.
  split.
    apply H.
  constructor.
Qed.
