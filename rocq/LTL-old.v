Require Import Program.
(* Require Import FunctionalExtensionality. *)
Require Import Coq.Lists.List.
Require Import Coq.Classes.Equivalence.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.
Require Import Equations.EqDec.

Open Scope program_scope.
Open Scope list_scope.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section LTL.

Variable a : Type.              (* The type of entries in the trace *)
Variable b : Type.              (* The type of data derived from each entry *)

Definition Stream := list a.

Inductive LTL : Type :=
  (* Boolean layer *)
  | Top
  | Bottom
  | Query (v : a -> option b)
  | And (p q : LTL)
  | Or (p q : LTL)
  | Impl (p q : LTL)

  (* Temporal layer *)
  | Next (p : LTL)
  | Eventually (p : LTL)
  | Until (p q : LTL)
  | Always (p : LTL).

Notation "⊤"       := Top             (at level 50).
Notation "⊥"       := Bottom          (at level 50).
Notation "¬ x"     := (Impl x Bottom) (at level 50).
Infix    "∧"       := And             (at level 50).
Infix    "∨"       := Or              (at level 50).
Infix    "→"       := Impl            (at level 50).
Notation "'X' x"   := (Next x)        (at level 50).
Notation "◇ x"     := (Eventually x)  (at level 50).
Notation "p 'U' q" := (Until p q)     (at level 50).
Notation "□ x"     := (Always x)      (at level 50).

Fixpoint LTL_size (p : LTL) : nat :=
  match p with
  | Query v      => 1
  | Top          => 1
  | Bottom       => 1
  | And p q      => 1 + LTL_size p + LTL_size q
  | Or p q       => 1 + LTL_size p + LTL_size q
  | Impl p q     => 1 + LTL_size p + LTL_size q
  | Next p       => 1 + LTL_size p
  | Eventually p => 1 + LTL_size p
  | Until p q    => 1 + LTL_size p + LTL_size q
  | Always p     => 1 + LTL_size p
  end.

Definition remaining (s : Stream) (p : LTL) := length s + LTL_size p.

Variable term : Type.

(* The [term] proposition must hold for any dangling cases, such as
   [EndOfTrace] and [UntilSing]. Choosing [term] to be [False] has the effect
   of requiring all matching formula to match some prefix of the input
   completely. *)
Inductive Witness : LTL -> Type :=
  | EndOfTrace (t : term) (l : LTL) : Witness l
  | IsTrue : Witness Top
  | Base q (w : b) : Witness (Query q)
  | Both `(P : Witness p) `(Q : Witness q) : Witness (p ∧ q)
  | InLeft `(P : Witness p) q : Witness (p ∨ q)
  | InRight p `(Q : Witness q) : Witness (p ∨ q)
  | Implied1 p q : Witness (p → q)
  | Implied2 `(P : Witness p) `(Q : Witness q) : Witness (p → q)
  | NextFwd `(P : Witness p) : Witness (X p)
  | EventuallyStop `(P : Witness p) : Witness (◇ p)
  | EventuallyFwd `(P : Witness p) : Witness (◇ p)
  | UntilPrf1 p `(Q : Witness q) : Witness (p U q)
  | UntilPrf2 `(P : Witness p) `(PS : Witness (p U q)) : Witness (p U q)
  | UntilPrf3 `(P : Witness p) q : Witness (p U q)
  | AlwaysPrf1 `(P : Witness p) `(PS : Witness (□ p)) : Witness (□ p)
  | AlwaysPrf2 `(P : Witness p) : Witness (□ p).

Fixpoint summation (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | x :: xs' => x + summation xs'
  end.

Lemma S_summation xs : S (summation xs) = summation (1 :: xs).
Proof. induction xs; simpl; auto. Qed.

Lemma plus_summation x xs : x + summation xs = summation (x :: xs).
Proof. induction xs; simpl; auto. Qed.

Lemma summation_plus x xs : summation xs + x = summation (x :: xs).
Proof.
  induction xs; simpl; auto.
  rewrite <- plus_assoc.
  rewrite IHxs.
  simpl.
  rewrite! plus_assoc.
  rewrite (plus_comm a0).
  reflexivity.
Qed.

Fixpoint Witness_size `(p : Witness L) : nat :=
  match p with
  | EndOfTrace t l   => 1 + LTL_size l
  | IsTrue           => 1
  | Base _ w         => 1
  | Both p q         => 1 + Witness_size p + Witness_size q
  | InLeft p _       => 1 + Witness_size p
  | InRight _ q      => 1 + Witness_size q
  | Implied1 _ _     => 1
  | Implied2 p q     => 1 + Witness_size p + Witness_size q
  | NextFwd p        => 1 + Witness_size p
  | EventuallyStop p => 1 + Witness_size p
  | EventuallyFwd p  => 1 + Witness_size p
  | UntilPrf1 p q    => 1 + Witness_size q
  | UntilPrf2 p q    => 1 + Witness_size p + Witness_size q
  | UntilPrf3 p q    => 1 + Witness_size p
  | AlwaysPrf1 p ps  => 1 + Witness_size p + Witness_size ps
  | AlwaysPrf2 p     => 1 + Witness_size p
  end.

Lemma Witness_not_empty `(p : Witness l) : Witness_size p > 0.
Proof. induction p; simpl; omega. Qed.

(*
Inductive Subterm : Witness -> Witness -> Prop :=
  | InclBoth1 p q        : Subterm p (Both p q)
  | InclBoth2 p q        : Subterm q (Both p q)
  | InclInLeft p         : Subterm p (InLeft p)
  | InclInRight q        : Subterm q (InRight q)
  | InclImplied1 p q     : Subterm p (Implied p q)
  | InclImplied2 p q     : Subterm q (Implied p q)
  | InclNextFwd p        : Subterm p (NextFwd p)
  | InclEventuallyStop p : Subterm p (EventuallyStop p)
  | InclEventuallyFwd p  : Subterm p (EventuallyFwd p)
  | InclUntilPrf1 p ps q : Subterm p (UntilPrf (p :: ps) q)
  | InclUntilPrf2 ps q   : Subterm q (UntilPrf ps q)
  | InclUntilPrf3 p ps q : Subterm (UntilPrf ps p) (UntilPrf (p :: ps) q)
  | InclAlwaysPrf1 p ps  : Subterm p (AlwaysPrf (p :: ps))
  | InclAlwaysPrf2 p ps  : Subterm (AlwaysPrf ps) (AlwaysPrf (p :: ps)).

Definition Subterm_inv_t : forall x y, Subterm x y -> Prop.
Proof.
  intros [] [] f;
  match goal with
  | [ H : Subterm ?X (Both ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Meet1 _ _ \/ f = Meet2 _ _)
      | exact (f = Meet1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Meet2 _ _)
      | exact False ] ]
  | [ H : Subterm ?X (Join ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Join1 _ _ \/ f = Join2 _ _)
      | exact (f = Join1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Join2 _ _)
      | exact False ] ]
  | _ => exact False
  end.
Defined.

Corollary Subterm_inv x y f : Subterm_inv_t x y f.
Proof.
  pose proof Term_eq_dec.
  destruct f, t1, t2; simpl;
  repeat destruct (Term_eq_dec _ _); subst;
  try (rewrite e || rewrite <- e);
  try (rewrite e0 || rewrite <- e0);
  try congruence;
  try rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto; simpl; intuition;
  try rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto; simpl; intuition.
Qed.

Program Instance Subterm_Irreflexive : Irreflexive Subterm.
Next Obligation.
  repeat intro.
  pose proof (Subterm_inv _ _ H0).
  inversion H0; subst; simpl in *.
  - now apply (Meet_acc_l x t2).
  - now apply (Meet_acc_r t1 x).
  - now apply (Join_acc_l x t2).
  - now apply (Join_acc_r t1 x).
Qed.

Lemma Subterm_wf : well_founded Subterm.
Proof.
  constructor; intros.
  inversion H0; subst; simpl in *;
  induction y;
  induction t1 || induction t2;
  simpl in *;
  constructor; intros;
  inversion H1; subst; clear H1;
  try (apply IHy1; constructor);
  try (apply IHy2; constructor).
Defined.
*)

(* Local Obligation Tactic := program_simpl; simpl; try constructor. *)
Local Obligation Tactic :=
  program_simpl; simpl;
  try first
      [ omega
      | repeat split; repeat intro;
        repeat match goal with
               [ H : _ /\ _ |- _ ] => destruct H
               end;
        subst; discriminate
      ].

Fixpoint Verify (T : Stream) `(W : Witness L) : Prop :=
  match W with
  | EndOfTrace t l   => l <> Top
  | IsTrue           => True
  | Base q w         => match T with x :: _ => q x = Some w | _ => False end
  | Both P Q         => Verify T P /\ Verify T Q
  | InLeft P _       => Verify T P
  | InRight _ Q      => Verify T Q
  | Implied1 _ _     => True
  | Implied2 P Q     => Verify T P -> Verify T Q
  | NextFwd P        => match T with _ :: xs => Verify xs P | _ => False end
  | EventuallyStop P => Verify T P
  | EventuallyFwd P  => match T with _ :: xs => Verify xs P | _ => False end
  | UntilPrf1 _ Q    => Verify T Q
  | UntilPrf2 P PS   => match T with x :: xs => Verify T P /\ Verify xs PS | _ => False end
  | UntilPrf3 P _    => match T with [x] => Verify [x] P | _ => False end
  | AlwaysPrf1 P PS  => match T with x :: xs => Verify T P /\ Verify xs PS | _ => False end
  | AlwaysPrf2 P     => match T with [x] => Verify [x] P | _ => False end
  end.

Local Obligation Tactic := program_simpl; unfold remaining; simpl; omega.

Inductive Stepper : Stream -> LTL -> Type :=
  | StepStream                : forall x xs L,
      Stepper xs L          -> Stepper (x :: xs) L
  | StepAnd1 (p q : LTL)      : forall T,
      Stepper T p           -> Stepper T (And p q)
  | StepAnd2 (p q : LTL)      : forall T,
      Stepper T q           -> Stepper T (And p q)
  | StepOr1 (p q : LTL)       : forall T,
      Stepper T p           -> Stepper T (Or p q)
  | StepOr2 (p q : LTL)       : forall T,
      Stepper T q           -> Stepper T (Or p q)
  | StepImpl1 (p q : LTL)     : forall T,
      Stepper T p           -> Stepper T (Impl p q)
  | StepImpl2 (p q : LTL)     : forall T,
      Stepper T q           -> Stepper T (Impl p q)
  | StepNext (p : LTL)        : forall x xs,
      Stepper xs p          -> Stepper (x :: xs) (Next p)
  | StepEventually1 (p : LTL) : forall T,
      Stepper T p           -> Stepper T (Eventually p)
  | StepEventually2 (p : LTL) : forall x xs,
      Stepper xs p          -> Stepper (x :: xs) (Eventually p)
  | StepUntil1 (p q : LTL)    : forall T,
      Stepper T q           -> Stepper T (Until p q)
  | StepUntil2 (p q : LTL)    : forall x xs,
      Stepper [x] p         -> Stepper (x :: xs) (Until p q)
  | StepUntil3 (p q : LTL)    : forall T,
      Stepper T p           -> Stepper T (Until p q)
  | StepUntil4 (p q : LTL)    : forall x xs,
      Stepper xs (p U q)    -> Stepper (x :: xs) (Until p q)
  | StepAlways1 (p : LTL)     : forall T,
      Stepper T p           -> Stepper T (Always p)
  | StepAlways2 (p : LTL)     : forall x xs,
      Stepper xs (Always p) -> Stepper (x :: xs) (Always p).

Program Fixpoint Compute' (t : option term) (T : Stream) (L : LTL) {wf (Stepper T L)} : option (Witness L) :=
  match L with
  | Top          => Some IsTrue
  | Bottom       => None
  | Query v      => match T with
                    | x :: _ =>
                      match v x with
                      | None => None
                      | Some r => Some (Base v r)
                      end
                    | _ =>
                      match t with
                      | None => None
                      | Some t => Some (EndOfTrace t (Query v))
                      end
                    end
  | And p q      => match Compute' t T p with
                    | None   => None
                    | Some P =>
                      match Compute' t T q with
                      | None   => None
                      | Some Q => Some (Both P Q)
                      end
                    end
  | Or p q       => match Compute' t T p with
                    | None   =>
                      match Compute' t T q with
                      | None   => None
                      | Some Q => Some (InRight p Q)
                      end
                    | Some P => Some (InLeft P q)
                    end
  | Impl p q     => match Compute' t T p with
                    | None   => Some (Implied1 p q)
                    | Some P =>
                      match Compute' t T q with
                      | None   => None
                      | Some Q => Some (Implied2 P Q)
                      end
                    end
  | Next p       => match T with
                    | _ :: xs =>
                      match Compute' t xs p with
                      | None => None
                      | Some P => Some (NextFwd P)
                      end
                    | _ =>
                      match t with
                      | None => None
                      | Some t => Some (EndOfTrace t (Next p))
                      end
                    end
  | Eventually p => match T with
                    | x :: xs =>
                      match Compute' t (x :: xs) p with
                      | None =>
                        match Compute' t xs p with
                        | None => None
                        | Some P => Some (EventuallyFwd P)
                        end
                      | Some P => Some (EventuallyStop P)
                      end
                    | _ =>
                      match t with
                      | None => None
                      | Some t => Some (EndOfTrace t (Eventually p))
                      end
                    end
  | Until p q    => match T with
                    | x :: xs =>
                      match Compute' t (x :: xs) q with
                      | Some Q => Some (UntilPrf1 p Q)
                      | None =>
                        match xs with
                        | [] =>
                          match Compute' t [x] p with
                          | Some P => Some (UntilPrf3 P q)
                          | None => None
                          end
                        | _ =>
                          match Compute' t (x :: xs) p with
                          | None => None
                          | Some P =>
                            match Compute' t xs (p U q) with
                            | Some Q => Some (UntilPrf2 P Q)
                            | None => None
                            end
                          end
                        end
                      end
                    | _ =>
                      match t with
                      | None => None
                      | Some t => Some (EndOfTrace t (Until p q))
                      end
                    end
  | Always p     => match T with
                    | x :: xs =>
                      match Compute' t (x :: xs) p with
                      | None => None
                      | Some P =>
                        match xs with
                        | [] => Some (AlwaysPrf2 P)
                        | _ =>
                          match Compute' t xs (Always p) with
                          | None => None
                          | Some PS => Some (AlwaysPrf1 P PS)
                          end
                        end
                      end
                    | _ =>
                      match t with
                      | None => None
                      | Some t => Some (EndOfTrace t (Always p))
                      end
                    end
  end.

Fixpoint Compute' (t : option term) (T : Stream) (L : LTL) (n : nat) : option (Witness L) :=
  match n with
  | O => None
  | S n' =>
    match L with
    | Top          => Some IsTrue
    | Bottom       => None
    | Query v      => match T with
                      | x :: _ => Some (Base v (v x))
                      | _ =>
                        match t with
                        | None => None
                        | Some t => Some (EndOfTrace t (Query v))
                        end
                      end
    | And p q      => match Compute' t T p n' with
                      | None   => None
                      | Some P =>
                        match Compute' t T q n' with
                        | None   => None
                        | Some Q => Some (Both P Q)
                        end
                      end
    | Or p q       => match Compute' t T p n' with
                      | None   =>
                        match Compute' t T q n' with
                        | None   => None
                        | Some Q => Some (InRight p Q)
                        end
                      | Some P => Some (InLeft P q)
                      end
    | Impl p q     => match Compute' t T p n' with
                      | None   => Some (Implied1 p q)
                      | Some P =>
                        match Compute' t T q n' with
                        | None   => None
                        | Some Q => Some (Implied2 P Q)
                        end
                      end
    | Next p       => match T with
                      | _ :: xs =>
                        match Compute' t xs p n' with
                        | None => None
                        | Some P => Some (NextFwd P)
                        end
                      | _ =>
                        match t with
                        | None => None
                        | Some t => Some (EndOfTrace t (Next p))
                        end
                      end
    | Eventually p => match T with
                      | x :: xs =>
                        match Compute' t (x :: xs) p n' with
                        | None =>
                          match Compute' t xs p n' with
                          | None => None
                          | Some P => Some (EventuallyFwd P)
                          end
                        | Some P => Some (EventuallyStop P)
                        end
                      | _ =>
                        match t with
                        | None => None
                        | Some t => Some (EndOfTrace t (Eventually p))
                        end
                      end
    | Until p q    => match T with
                      | x :: xs =>
                        match Compute' t (x :: xs) q n' with
                        | Some Q => Some (UntilPrf1 p Q)
                        | None =>
                          match xs with
                          | [] =>
                            match Compute' t [x] p n' with
                            | Some P => Some (UntilPrf3 P q)
                            | None => None
                            end
                          | _ =>
                            match Compute' t (x :: xs) p n' with
                            | None => None
                            | Some P =>
                              match Compute' t xs (p U q) n' with
                              | Some Q => Some (UntilPrf2 P Q)
                              | None => None
                              end
                            end
                          end
                        end
                      | _ =>
                        match t with
                        | None => None
                        | Some t => Some (EndOfTrace t (Until p q))
                        end
                      end
    | Always p     => match T with
                      | x :: xs =>
                        match Compute' t (x :: xs) p n' with
                        | None => None
                        | Some P =>
                          match xs with
                          | [] => Some (AlwaysPrf2 P)
                          | _ =>
                            match Compute' t xs (Always p) n' with
                            | None => None
                            | Some PS => Some (AlwaysPrf1 P PS)
                            end
                          end
                        end
                      | _ =>
                        match t with
                        | None => None
                        | Some t => Some (EndOfTrace t (Always p))
                        end
                      end
    end
  end.

Definition Compute (t : option term) (T : Stream) (L : LTL) :=
  Compute' t T L (remaining T L).

Lemma Compute'_Both t T p q n P1 P2 :
  Compute' t T p n = Some P1 ->
  Compute' t T q n = Some P2 ->
  Compute' t T (p ∧ q) n = Some (Both P1 P2).
Proof.
  generalize dependent p.
  generalize dependent q.
  generalize dependent T.
  generalize dependent t.
  induction n; simpl; intros.
    discriminate.
  destruct p, q; try discriminate;
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  - admit.
  - admit.
  -
  destruct n; simpl in *.
Abort.

Lemma Compute_Verified (t : option term) (T : Stream) (L : LTL) :
  forall P, Compute t T L = Some P -> Verify T P.
Proof.
  unfold Compute; intros.
  generalize dependent (remaining T L).
  induction n; simpl in *.
    discriminate.
  destruct P; simpl in *; intros; auto.
  - destruct l; simpl in *;
    inversion_clear H; discriminate.
  - destruct T; simpl in *.
      destruct t;
      inversion_clear H; discriminate.
    now inversion_clear H.
  - destruct (Compute' t T p n) eqn:?;
    destruct (Compute' t T q n) eqn:?; try discriminate.
    inversion H; subst; clear H.
    apply inj_pair2 in H1.
    apply inj_pair2 in H2.
    subst.
    apply IHn; clear IHn.
  - destruct p, q; simpl in *; admit.
  - destruct q; simpl in *; admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct T, p, t; simpl in *.
Admitted.

(*
Equations Verify (T : Stream) (L : LTL) (W : Witness L) : Prop
  by wf (Witness_size W) lt :=
  Verify _ _ (EndOfTrace _ l) with L := {
    | Top := False;
    | _   := l = L
  };

  Verify _ _ IsTrue with L := {
    | Top := True;
    | _   := False
  };

  Verify _ _ (Base _ b) with L := {
    | Query q with T := {
        | x :: _ := q x b;
        | _      := False
      };
    | _ := False
  };

  Verify _ _ (Both P Q) with L := {
    | p ∧ q := Verify T p P /\ Verify T q Q;
    | _     := False
  };

  Verify _ _ (InLeft P _) with L := {
    | p ∨ _ := Verify T p P;
    | _     := False
  };

  Verify _ _ (InRight _ Q) with L := {
    | _ ∨ q := Verify T q Q;
    | _     := False
  };

  Verify _ _ (Implied P Q) with L := {
    | p → q := Verify T p P -> Verify T q Q;
    | _     := False
  };

  Verify _ _ (NextFwd P) with L := {
    | X p with T := {
        | _ :: xs := Verify xs p P;
        | _       := False
      };
    | _ := False
  };

  Verify _ _ (EventuallyStop P) with L := {
    | ◇ p := Verify T p P;
    | _   := False
  };

  Verify _ _ (EventuallyFwd P) with L := {
    | ◇ _ with T := {
        | _ :: xs := Verify xs L P;
        | _       := False
      };
    | _ := False
  };

  Verify _ _ (UntilPrf1 PS Q) with L := {
    | p U q with T := {
        | [] with PS := {
            | [] := Verify T q Q;
            | _  := False
          };
        | [x] with PS := {
            | [P] with Q := {
                | EndOfTrace _ l := l = q /\ Verify [x] p P;
                | _   := False
              };
            | _   := False
          };
        | x :: xs with PS := {
            | P :: PS' :=
              Verify (x :: xs) p P /\ Verify xs (p U q) (UntilPrf PS' P);
            | _   := False
          }
      };
    | _ := False
  };

  Verify _ _ (AlwaysPrf PS) with L := {
    | □ p with T := {
        | [] := False;
        | [x] with PS := {
            | [P] := Verify [x] p P;
            | _   := False
          };
        | x :: xs with PS := {
            | P :: PS' :=
              Verify (x :: xs) p P /\ Verify xs (□ p) (AlwaysPrf PS');
            | _   := False
          }
      };
    | _ := False
  }.
Next Obligation. pose proof (Witness_not_empty Q); simpl; omega. Defined.
Next Obligation. pose proof (Witness_not_empty P); simpl; omega. Defined.
Next Obligation.
  induction T, L, W; simpl;
  repeat try constructor.



  Verify _         Top       (EndOfTrace _ _)                := False;
  Verify _         _         (EndOfTrace _ l)                := l = L;
  Verify _         Top       IsTrue                          := True;
  Verify (x :: _)  (Query q) (Base b)                        := q x b;
  Verify _         (p ∧ q)   (Both P Q)                      := Verify T p P /\ Verify T q Q;
  Verify _         (p ∨ _)   (InLeft P)                      := Verify T p P;
  Verify _         (_ ∨ q)   (InRight Q)                     := Verify T q Q;
  Verify _         (p → q)   (Implied P Q)                   := Verify T p P -> Verify T q Q;
  Verify (_ :: xs) (X p)     (NextFwd P)                     := Verify xs p P;
  Verify _         (◇ p)     (EventuallyStop P)              := Verify T p P;
  Verify (_ :: xs) _         (EventuallyFwd P)               := Verify xs L P;
  Verify [x]       (p U _)   (UntilPrf [P] (EndOfTrace _ _)) := Verify [x] p P;
  Verify _         (_ U q)   (UntilPrf [] Q)                 := Verify T q Q;
  Verify (x :: xs) (p U q)   (UntilPrf (P :: PS) _)          :=
    Verify (x :: xs) p P /\ Verify xs (p U q) (UntilPrf PS P);

  Verify [x]       (□ p) (AlwaysPrf [P])       := Verify [x] p P;
  Verify (x :: xs) (□ p) (AlwaysPrf (P :: PS)) :=
    Verify (x :: xs) p P /\ Verify xs (□ p) (AlwaysPrf PS);

  Verify _ _ _ := False.

Next Obligation. pose proof (Witness_not_empty W); simpl; omega. Defined.
Next Obligation. pose proof (Witness_not_empty W); simpl; omega. Defined.
Next Obligation. pose proof (Witness_not_empty P); simpl; omega. Defined.
Next Obligation. pose proof (Witness_not_empty P); simpl; omega. Defined.
*)

(*
(* The [term] proposition must hold for any dangling cases, such as
   [EndOfTrace] and [UntilSing]. Choosing [term] to be [False] has the effect
   of requiring all matching formula to match some prefix of the input
   completely. *)
Program Fixpoint Verify (T : Stream) (L : LTL) (W : Witness) {measure (Witness_size W)} : Prop :=
  match T, L, W with
  | _, ⊤, EndOfTrace _ _ => False
  | _, _, EndOfTrace _ l => l = L

  | _, ⊤, IsTrue => True

  | x :: xs, Query q, Base a b => q a b

  | _, p ∧ q, Both P Q          => Verify T p P /\ Verify T q Q

  | _, p ∨ q, InLeft P          => Verify T p P
  | _, p ∨ q, InRight Q         => Verify T q Q

  | _, p → q, Implied P Q       => Verify T p P -> Verify T q Q

  | x :: xs, X p, NextFwd P     => Verify xs p P

  | _, ◇ p, EventuallyStop P    => Verify T p P

  | x :: xs, _, EventuallyFwd P => Verify xs L P

  | [x],     p U q, UntilPrf [P]       (EndOfTrace _ _) => Verify [x] p P
  | x :: xs, p U q, UntilPrf []        Q                => Verify (x :: xs) q Q
  | x :: xs, p U q, UntilPrf (P :: PS) Q                =>

    Verify (x :: xs) p P /\ Verify xs (p U q) (UntilPrf PS P)

  | [x],     □ p, AlwaysPrf [P]       => Verify [x] p P
  | x :: xs, □ p, AlwaysPrf (P :: PS) =>

    Verify (x :: xs) p P /\ Verify xs (□ p) (AlwaysPrf PS)

  | _, _, _ => False
  end.
Next Obligation.
  pose proof (Witness_not_empty Q).
  simpl; omega.
Defined.
Next Obligation.
  pose proof (Witness_not_empty P).
  simpl; omega.
Defined.
*)

Notation "T ⊢ L ⟿ P" := (@Verify T L P) (at level 80).

Definition impl (φ ψ : LTL) := ¬φ ∨ ψ.

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 50).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition release (φ ψ : LTL) := ¬(¬φ U ¬ψ).
Notation "p 'R' q" := (release p q) (at level 50).

Definition Witness_equiv {p} (P : Witness p) (Q : Witness p) : Prop.
Admitted.

Definition ltl_equiv (p q : LTL) : Prop :=
  forall s (P : Witness p) (Q : Witness q),
    Verify s P <-> Verify s Q.

Local Obligation Tactic := program_simpl.

(*
Program Instance Equivalence_ltl_equiv : Equivalence ltl_equiv.
Next Obligation.
  repeat intro; split; auto.
Qed.
Next Obligation.
  repeat intro; intros.
  now symmetry.
Qed.
Next Obligation.
  repeat intro; intros.
  specialize (H s).
  specialize (H0 s).
  now rewrite H, H0.
Qed.
*)

Infix "≈" := equiv (at level 90).

Ltac end_of_trace := apply EndOfTrace; [auto|intro; discriminate].

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ltl_equiv (◇ ψ) (⊤ U ψ).
Proof.
  repeat intro; split; intros.

Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof.
  repeat intro; split; intros.
  - induction s; simpl.
      inversion P.
        now constructor.
      now apply UntilNil.
    inversion_clear H.
      now constructor.
    apply UntilCons; auto.
    now constructor.
  - induction s; intros.
      inversion_clear H.
        now constructor.
      now apply EventuallyStop.
    inversion_clear H.
    + now constructor.
    + now apply EventuallyFwd; auto.
    + apply EventuallyFwd.
      now end_of_trace.
Qed.

Lemma witness_neg s φ : @Witness False s (¬ φ) <-> ~ (@Witness False s φ).
Proof.
  split; repeat intro.
  - inversion_clear H; auto.
    admit.
  - induction s.
    + constructor.
      apply H.
        admit.
      admit.
    + admit.
Abort.

(* ψ always remains true *)
Lemma always_remains_true (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. Abort.

Lemma always_remains_true' (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Proof. Abort.

Definition weakUntil (φ ψ : LTL) := (φ U ψ) ∨ □ φ.
Notation "p 'W' q" := (weakUntil p q) (at level 50).

Definition strongRelease (φ ψ : LTL) := ψ U (φ ∧ ψ).
Notation "p 'M' q" := (strongRelease p q) (at level 50).

Lemma foo2 (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. Abort.

Lemma foo3 (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. Abort.

Lemma foo4 (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. Abort.

Lemma foo5 (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. Abort.

Lemma foo6 (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Proof. Abort.

Lemma foo7 (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. Abort.

Lemma foo8 (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. Abort.

(** Distributivity *)

Lemma foo10 (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof. Abort.

Lemma foo11 (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Proof. Abort.

Lemma foo12 (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
Proof. Abort.

Lemma foo13 (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. Abort.

Lemma foo14 (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Proof. Abort.

Lemma foo15 (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Proof. Abort.

Lemma foo16 (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Proof. Abort.

(** Negation propagation *)

Lemma foo18 (φ : LTL) : ¬(X φ) ≈ X ¬φ.
Proof.
  repeat intro; split; intros.
  - induction s.
      inversion_clear H.
        end_of_trace.
    inversion_clear H.
  - induction s; intros.
      inversion_clear H.
        end_of_trace.
    inversion_clear H.

    + now constructor.
    + now apply EventuallyFwd; auto.
    + apply EventuallyFwd.
      now end_of_trace.
Qed.

Lemma foo19 (φ : LTL) : ¬(◇ φ) ≈ □ ¬φ.
Proof. Abort.

Lemma foo20 (φ ψ : LTL) : ¬ (φ U ψ) ≈ (¬φ R ¬ψ).
Proof. Abort.

Lemma foo21 (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof. Abort.

Lemma foo22 (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. Abort.

Lemma foo23 (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof. Abort.

Lemma foo24 (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof. Abort.

(** Special Temporal properties *)

Lemma foo25 (φ : LTL) :   ◇ φ ≈ ◇ ◇ φ.
Proof. Abort.

Lemma foo26 (φ : LTL) :   □ φ ≈ □ □ φ.
Proof. Abort.

Lemma foo27 (φ ψ : LTL) : φ U ψ ≈ φ U (φ U ψ).
Proof. Abort.

Lemma foo28 (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)).
Proof. Abort.

Lemma foo29 (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ X(φ W ψ)).
Proof. Abort.

Lemma foo30 (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)).
Proof. Abort.

Lemma foo31 (φ : LTL) :   □ φ ≈ φ ∧ X(□ φ).
Proof. Abort.

Lemma foo32 (φ : LTL) :   ◇ φ ≈ φ ∨ X(◇ φ).
Proof. Abort.

End LTL.

(* Weak Interpretation, where an EndOfTrace is considered a match. *)
Notation "T ⊢~ L ⟿ P" := (@Verify True T L P) (at level 80).

Definition ltl_strong_equiv (p q : LTL) : Prop :=
  forall s P, @Verify False s p P <-> @Verify False s q P.

Program Instance Equivalence_ltl_strong_equiv : Equivalence ltl_strong_equiv | 9.
Next Obligation.
  repeat intro; split; auto.
Qed.
Next Obligation.
  repeat intro; intros.
  now symmetry.
Qed.
Next Obligation.
  repeat intro; intros.
  specialize (H s).
  specialize (H0 s).
  now rewrite H, H0.
Qed.

Infix "≈[strong]" := ltl_strong_equiv (at level 90).
