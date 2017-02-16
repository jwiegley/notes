Require Import Fiat.ADT Fiat.ADTNotation Coq.Sets.Ensembles PeanoNat.

Definition Stream (A : Type) := nat -> Comp A.

Definition nth_smallest `{StrictOrder A R} (n : nat) (s : Comp A) : Comp A :=
  { i | exists xs, (In _ s i <-> List.In i xs)
          /\ Sorted.Sorted R xs /\ i = List.nth n xs i }.

Goal refine (nth_smallest 1 { i | i = 1 \/ i = 7 \/ i = 5 }) (ret 5).
Proof.
  unfold nth_smallest.
  refine pick val _.
    reflexivity.
  eexists; split; firstorder.
Qed.

Definition map {A B} (f : A -> B -> Prop) (s : Stream A) : Stream B := fun n =>
  { b : B | exists a, s n a /\ f a b }.

Definition filter {A} (f : A -> Prop) (s : Stream A) : Stream A := fun n =>
  i <- nth_smallest n { i | exists x, s i x /\ f x };
  s i.

Goal refine (filter Even.even (fun x => ret x) 3) (ret 6).
Proof.
  unfold filter, nth_smallest.
  refine pick val _.
    simplify with monad laws.
    reflexivity.
  eexists; split; firstorder.
  eexists; split; firstorder.
  repeat constructor.
Qed.

Definition lexi_lt (x y : nat * nat) : Prop :=
  fst x < fst y \/ (fst x = fst y /\ snd x < snd y).

Program Instance StrictOrder_lexi : StrictOrder lexi_lt.
Obligation 1.
  intros [? ?].
  destruct 1; intuition.
Qed.
Obligation 2.
  intros [? ?] [? ?] [? ?].
  destruct 1; destruct 1;
  solve [ left; intuition
        | right; intuition ].
Qed.

Definition flatten {A} (s : Stream (Stream A)) : Stream A := fun n =>
  `(i, j) <- nth_smallest n
     { p | forall i j : nat, p = (i, j) -> exists s' x, s i s' /\ s' j x };
  s' <- s i;
  s' j.

Definition bind {A B} (f : A -> Stream B -> Prop) (s : Stream A) : Stream B :=
  flatten (map f s).

Definition stream_1_to_2 : Stream nat := fun n =>
  ret (List.nth n [1;2] n).

Definition stream_3_to_inf : Stream nat := fun n =>
  ret (n + 3).

Definition stream_of_streams : Stream (Stream nat) := fun n =>
  ret (List.nth n [stream_1_to_2; stream_3_to_inf] (fun n => ret n)).

Definition stream_of_streams_flattened : Stream nat := fun n =>
  ret (If n <? 2
       Then List.nth n [1; 2] n
       Else n + 1).

Lemma If_Then_Else_fst : forall b A B (t e : A * B),
  fst (If b Then t Else e) = If b Then fst t Else fst e.
Proof. destruct b; auto. Qed.

Lemma If_Then_Else_snd : forall b A B (t e : A * B),
  snd (If b Then t Else e) = If b Then snd t Else snd e.
Proof. destruct b; auto. Qed.

Goal forall n, refine (flatten stream_of_streams n)
                      (stream_of_streams_flattened n).
Proof.
  unfold flatten, stream_of_streams, stream_of_streams_flattened,
         nth_smallest, Bind2, stream_1_to_2, stream_3_to_inf; intros.
  refine pick val (If n <? 2
                   Then (0, n)
                   Else (1, n - 2)).
    simplify with monad laws; simpl.
    rewrite !If_Then_Else_fst, !If_Then_Else_snd; simpl.
    destruct n; simpl.
      reflexivity.
    destruct n; simpl.
      reflexivity.
    rewrite Nat.sub_0_r, !plus_n_Sm.
    reflexivity.
  Ltac expect v :=
    exists v; simpl;
    split; intuition;
    apply PickComputes; intros;
    inversion H; subst;
    do 2 eexists;
    split; reflexivity.
  destruct n; simpl; [ expect [(0,0)]%list |].
  destruct n; simpl; [ expect [(0,1)]%list |].
  expect [(1,n)]%list.
Qed.

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

Definition guard (P : Prop) : Comp () := { u : () | P }.

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

Lemma Forall_append : forall A (P : A -> Prop) xs ys,
   List.Forall P xs /\ List.Forall P ys <-> List.Forall P (xs ++ ys).
Proof.
  intros A P.
  induction xs as [|x xs IHxs]; simpl.
    split; intuition.
  split.
    constructor;
    destruct H;
    inversion H.
      assumption.
    apply (IHxs ys).
    intuition.
  intro H.
  split.
    constructor;
    inversion H.
      assumption.
    subst.
    apply IHxs in H3.
    intuition.
  inversion H; subst.
  apply IHxs in H3.
  intuition.
Qed.

Lemma Sorted_app {A : Type} {xs ys : list A} {R : A -> A -> Prop}
  `{Transitive _ R} :
  Sorted.Sorted R xs -> Sorted.Sorted R ys
    -> List.Forall (fun x => List.Forall (fun y => R x y) ys) xs
    -> Sorted.Sorted R (xs ++ ys).
Proof.
  intros.
  generalize dependent ys.
  induction H0; simpl; intros; auto.
  destruct H1; simpl in *.
    constructor; trivial.
    destruct ys; auto.
    constructor.
    repeat apply List.Forall_inv in H3.
    assumption.
  constructor.
    apply IHSorted; trivial.
    inversion H3.
    assumption.
  constructor.
  inversion H3.
  assumption.
Qed.

Lemma Forall_rev : forall A (xs : list A) P,
  List.Forall P xs -> List.Forall P (List.rev xs).
Proof.
  intros.
  induction xs; simpl; auto.
  apply Forall_append.
  inversion H.
  intuition.
Qed.

Lemma length_nat_rec : forall (A : Set) f n,
  length (nat_rec (fun _ : nat => list A) []%list
                  (fun n xs => f n :: xs)%list n) = n.
Proof.
  intros.
  unfold nat_rec.
  induction n; auto; simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma nth_smallest_diag_left : forall i,
  refine {n : nat | exists s0, nth_smallest n s0 (i, 0)} (ret i).
Proof.
  unfold nth_smallest; intros.
  intros ??.
  apply Return_inv in H; subst.
  apply PickComputes.
  exists (ret (v, 0)).
  exists (List.rev (nat_rec (fun _ => list (nat * nat))
                            []%list (fun n xs => ((n, 0) :: xs)%list) (v + 1))).
  split.
    split; intros.
     induction v; simpl.
        left; trivial.
      apply List.in_rev.
      rewrite List.rev_unit.
      left.
      rewrite NPeano.Nat.add_1_r.
      reflexivity.
    constructor.
  split.
    induction v; simpl.
      repeat constructor.
    apply Sorted_app; auto.
    apply Forall_rev.
    clear IHv.
    induction v; simpl;
    repeat constructor.
    apply List.Forall_impl
     with (P:=(fun x => List.Forall (fun y => lexi_lt x y) [(v + 1, 0)])).
      intros.
      destruct a; simpl in *.
      inversion H; subst; clear H.
      constructor.
        destruct H2; simpl in H;
        repeat constructor;
        intuition.
      assumption.
    apply IHv.
  destruct v; simpl.
    reflexivity.
  rewrite List.app_nth2; simpl;
  rewrite List.rev_length, length_nat_rec.
    destruct (match v + 1 with
              | 0 => S v
              | S l => v - l
              end).
      rewrite NPeano.Nat.add_1_r; auto.
    destruct n; auto.
  rewrite NPeano.Nat.add_1_r; auto.
Qed.

Lemma nth_smallest_diag_right : forall i,
  refine {n : nat | exists s0, nth_smallest n s0 (0, i)} (ret i).
Proof.
  unfold nth_smallest; intros.
  intros ??.
  apply Return_inv in H; subst.
  apply PickComputes.
  exists (ret (0, v)).
  exists (List.rev (nat_rec (fun _ => list (nat * nat))
                            []%list (fun n xs => ((0, n) :: xs)%list) (v + 1))).
  split.
    split; intros.
     induction v; simpl.
        left; trivial.
      apply List.in_rev.
      rewrite List.rev_unit.
      left.
      rewrite NPeano.Nat.add_1_r.
      reflexivity.
    constructor.
  split.
    induction v; simpl.
      repeat constructor.
    apply Sorted_app; auto.
    apply Forall_rev.
    clear IHv.
    induction v; simpl.
      right.
        constructor; trivial.
        right; intuition.
      repeat constructor.
    constructor.
      constructor.
        right; intuition.
      constructor.
    apply List.Forall_impl
     with (P:=(fun x => List.Forall (fun y => lexi_lt x y) [(0, v + 1)])).
      intros.
      destruct a; simpl in *.
      inversion H; subst; clear H.
      constructor.
        destruct H2; simpl in H.
          right; intuition.
        destruct H; subst.
        right; intuition; simpl.
        constructor.
        apply H0.
      assumption.
    apply IHv.
  destruct v; simpl.
    reflexivity.
  rewrite List.app_nth2; simpl;
  rewrite List.rev_length, length_nat_rec.
    destruct (match v + 1 with
              | 0 => S v
              | S l => v - l
              end).
      rewrite NPeano.Nat.add_1_r; auto.
    destruct n; auto.
  rewrite NPeano.Nat.add_1_r; auto.
Qed.

Theorem for_yield_f `(f : b -> Pipe x' x c' c ()) z :
  forP (yield z) f =| f z.
Proof.
  unfold refine_pipe, forP, yield; simpl; intros.
  destruct (f z).
  setoid_rewrite nth_smallest_diag_right.
  autorewrite with monad laws; reflexivity.
Qed.

Theorem for_yield `(s : Pipe x' x () b ()) :
  forP s yield =| s.
Proof.
  unfold refine_pipe, forP, yield; simpl; intros.
  destruct s.
  setoid_rewrite nth_smallest_diag_left.
  autorewrite with monad laws; reflexivity.
Qed.

Definition curry `(f : (a * b) -> c) (x : a) (y : b) : c := f (x, y).
Definition uncurry `(f : a -> b -> c) (p : a * b) : c := f (fst p) (snd p).

Lemma curry_uncurry : forall `(f : a -> b -> c), curry (uncurry f) = f.
Proof. firstorder. Qed.

Lemma uncurry_curry : forall `(f : (a * b) -> c), uncurry (curry f) = f.
Proof.
  unfold curry, uncurry; intros.
  extensionality p.
  rewrite <- surjective_pairing; auto.
Qed.

Definition _bind `(p : Pipe a' a b' b r) `(f : r -> Pipe a' a b' b r') :
  Pipe a' a b' b r'.
Admitted.
  (* {| segment := *)
  (*      fun inc out => *)
  (*        segment p inc *)
  (*                (fun b i => *)
  (*                   segment (f b) inc *)
  (*                           (fun c j => *)
  (*                              n <- { n | exists s, nth_smallest n s (i, j) }; *)
  (*                                out c n)) *)
  (*  ; proper := _ |}. *)

(*
p0 `_bind` f = go p0 where
    go p = case p of
        Request a' fa  -> Request a' (\a  -> go (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
        M          m   -> M (m >>= \p' -> return (go p'))
        Pure    r      -> f r
*)

Definition next `(p : Producer a r) : Comp (r + (a * Producer a r)) :=
  fun x =>
    match x with
    | inl x => forall inc out, segment p inc out x
    | inr (a, next) => forall inc out, exists r,
      segment next inc out r /\
      segment p inc (fun y _ _ => a = y) r
    end.

Program Definition empty {a : Type} : Producer' a () := fun _ _ =>
  {| segment := fun _ _ => ret tt
   ; proper  := _ |}.
Obligation 1. intros ??????; reflexivity. Qed.

Definition each `(xs : list a) : Producer' a () := fun _ _ =>
  List.fold_right (fun x p => _bind (yield x) (fun _ => p))
                  (empty _ _) xs.