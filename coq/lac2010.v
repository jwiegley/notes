(* This file has been tested with coq-8.4pl3 and works fine.
   It has also been tested with coq-8.5beta2, but some of the
   computations don't reduce well. *)
Require Import Streams ZArith List.
Open Scope Z_scope.

Infix "::" := Cons.

CoInductive zstream : Type :=
  cstr (x : Z) (s : zstream) | zipPlus (s1 s2 : zstream).


Definition zforce (s : zstream) :=
  match s with
    cstr x s' => cstr x s'
  | zipPlus s1 s2 => zipPlus s1 s2
  end.

Lemma zforce_eq : forall s, s = zforce s.
intros [x s' | s1 s2]; reflexivity.
Defined.

(* This expresses that the patch of zipPlus calls at the
  root of the argument zstream term is actually well-founded
  (in this case, this coincides with finite) *)
Inductive zf : zstream -> Prop :=
  cz1 : forall x s, zf (cstr x s)
| cz3 : forall s1 s2, zf s1 -> zf s2 -> zf (zipPlus s1 s2).

(* I do not use inversion to prove this lemma, because
  I want computation to behave well on this kind of terms. *)
Lemma zf_inv1 :
  forall s, zf s -> forall s1 s2, s = (zipPlus s1 s2) -> zf s1.
intros s h; case h; try (intros; discriminate).
intros s1 s2 h1 _ s3 s4 q; injection q; intros q2 q1; rewrite <- q1.
assumption.
Defined.

(* same comment as for zf_inv1. *)
Lemma zf_inv2 :
  forall s, zf s -> forall s1 s2, s = (zipPlus s1 s2) -> zf s2.
intros s h; case h; try (intros; discriminate).
intros s1 s2 _ h2 s3 s4 q; injection q; intros q2 q1; rewrite <- q2.
assumption.
Defined.

(* This expresses that any patch of zipPlus terms in the infinite
  expression given as argument is finite. *)
CoInductive zr : zstream -> Prop :=
  cs1 : forall x s, zr s -> zr (cstr x s)
| cs2 : forall s1 s2, zr s1 -> zr s2 -> zf s1 -> zf s2 ->
         zr (zipPlus s1 s2).

Lemma zr_to_zf : forall s, zr s -> zf s.
intros s h; case h; intros; constructor; assumption.
Defined.

Definition ex_zip1 : forall s, zf s -> Z * zstream.
fix 2.
intros s h; generalize (refl_equal s); pattern s at -1.
case s.
intros x s' _; exact (x, s').
intros s1 s2 q; case (ex_zip1 s1);[ | intros x1 s1'].
 exact (zf_inv1 s h s1 s2 q).
case (ex_zip1 s2);[ | intros x2 s2'].
 exact (zf_inv2 s h s1 s2 q).
exact (x1 + x2, zipPlus s1' s2').
Defined.

Scheme zf_ind2 := Induction for zf Sort Prop.

Lemma ex_zip1_correct :
   forall s h (h' : zr s), zr (snd (ex_zip1 s h)).
Proof.
intros s h; elim h using zf_ind2; simpl.
 intros x s' h'; inversion h'; assumption.
intros s1 s2 s1f IH1 s2f IH2 ps.
destruct (ex_zip1 s1 s1f) as [v1 w1]; destruct (ex_zip1 s2 s2f) as [v2 w2].
inversion ps; constructor; try apply zr_to_zf; auto.
Defined.

Definition qex_zip1 s (h : zr s) : Z * {s' | zr s'}.
Proof.
generalize (ex_zip1_correct s (zr_to_zf s h) h).
destruct (ex_zip1 s (zr_to_zf s h)) as [v w].
intros h'; split;[exact v | exists w; exact h'].
Defined.

CoFixpoint ztostream (s:zstream) (h:zr s) : Stream Z :=
  let (x, qs) := qex_zip1 s h in let (s', hs') := qs in
  x::ztostream s' hs'.

CoFixpoint fib : zstream :=
 cstr 0 (zipPlus fib (cstr 1 fib)).

Lemma zf_fib : zf fib.
rewrite zforce_eq; simpl zforce; constructor.
Defined.

Lemma zr_fib : zr fib.
cofix.
rewrite zforce_eq; simpl zforce;
 repeat constructor; apply zr_fib || apply zf_fib.
Defined.

Definition fib' := ztostream _ zr_fib.

Fixpoint take n s : list Z :=
  match n, s with O, _ => nil | S p, a::w => (a::take p w)%list end.

(* In coq-8.4pl3, this instance of "lazy" can be replaced with
   "vm_compute" and the behavior is nice, but in coq-8.5beta2,
   it returns a large un-evaluated symbolic expression. *)
Eval lazy in take 14 fib'.

(* Now a different presentation, using accessibility, the
  predicate that is used to defined well-founded relations. *)
Definition subzip x y :=
  exists z, y = zipPlus x z \/ y = zipPlus z x.

(* express directly that a tree is well-formed when the relation
  of sub-zip-term is well-founded everywhere in the tree. *)
CoInductive zw : zstream -> Prop :=
  cw1 : forall x s, zw s -> zw (cstr x s)
| cw2 : forall s1 s2,
  Acc subzip s1 -> Acc subzip s2 -> zw s1 -> zw s2 -> zw (zipPlus s1 s2).

Lemma zw_fib : zw fib.
cofix.
rewrite zforce_eq; simpl zforce.
constructor; constructor.
   constructor.
   intros y; rewrite (zforce_eq fib); simpl zforce.
   intros h; inversion h.
   destruct H as [H | H]; discriminate.
  constructor; intros y h; inversion h.
  destruct H as [H | H]; discriminate.
 assumption.
constructor; assumption.
Defined.

Lemma zw_inv1 : forall x s, zw (cstr x s) -> zw s.
intros x s h; inversion h; assumption.
Defined.

Lemma zw_acc : forall s, zw s -> Acc subzip s.
intros s h; inversion h.
 constructor; intros y h'; inversion h'; destruct H1; discriminate.
constructor; intros y; intros [z [H' | H']]; injection H';
 intros; subst; assumption.
Defined.

Definition qex_w_zip (s : zstream) : zw s -> Z * {s' | zw s'}.
intros h; assert (h' := zw_acc _ h); revert h.
apply (Fix_F (R:= subzip) (fun s => zw s -> Z * {s' | zw s'})).
 intros x; case x; [intros a s' f h | intros s1 s2 f h].
  split;[exact a | exists s'; exact (zw_inv1 _ _ h)].
 case (f s1).
   exists s2; left; reflexivity.
  inversion h; assumption.
 intros a1 qs1; case qs1; intros s1' q1.
 case (f s2).
   exists s1; right; reflexivity.
  inversion h; assumption.
 intros a2 qs2; case qs2; intros s2' q2.
 split.
  exact (a1 + a2).
 exists (zipPlus s1' s2'); constructor.
    apply zw_acc; assumption.
   apply zw_acc; assumption.
  assumption.
 assumption.
assumption.
Defined.

CoFixpoint ztostream' (s : zstream) (h : zw s) : Stream Z :=
  let (x, qs) := qex_w_zip s h in let (s', q) := qs in
  x::ztostream' s' q.

Definition wfib := ztostream' fib zw_fib.

Eval vm_compute in take 20 wfib.

(* Timing is much better than for fib'. *)