Require Import
  Coq.Program.Program
  Coq.Setoids.Setoid.

(* We use a typeclass so that resolution of [R] for the begin operation
   decides [R] for the remainder. As separate functions that each try to unify
   [R], it does not work. *)

Class Equational {A : Type} (R : relation A) := {
  _is_reflexive  :> Reflexive R;
  _is_transitive :> Transitive R;

  _begin_  {p q} (pq : R p q) : R p q := pq;
  _beginr_ {p q} (pq : R p q) `{Symmetric A R} : R q p := symmetry pq;
  final     p : R p p := reflexivity p;
  step_simpl    p {q}   (pq : R p q) : R p q := pq;
  _step_eqv     p {q r} (qr : R q r) (pq : R p q) : R p r := transitivity pq qr;
  _step_eqv_r  {p q} r  (pq : R p q) (qr : R q r) : R p r := transitivity pq qr;
  _step_sym_eqv p {q r} (qr : R q r) (qp : R q p) `{Symmetric A R} : R p r :=
    transitivity (symmetry qp) qr;
}.

(* For some of the methods above, [R] must be inferred from use before looking
   for a typeclass instance. Otherwise, using [begin] simply picks whichever
   instance was most recently defined and has the highest level. *)

Definition begin_ {A : Type} {R : relation A} {p q} (pq : R p q)
           `{E : Equational A R} : R p q :=
  @_begin_ A R E p q pq.

Definition beginr_ {A : Type} {R : relation A} {p q} (pq : R p q)
           `{E : Equational A R} `{S : Symmetric A R} : R q p :=
  @_beginr_ A R E p q pq S.

Definition step_eqv {A : Type} {R : relation A} p {q r}
           (qr : R q r) (pq : R p q) `{E : Equational A R} : R p r :=
  @_step_eqv A R E p q r qr pq.

Definition step_eqv_r {A : Type} {R : relation A} {p q} r
           (pq : R p q) (qr : R q r) `{E : Equational A R} : R p r :=
  @_step_eqv_r A R E p q r pq qr.

Definition step_sym_eqv {A : Type} {R : relation A} {p q} r
           (qr : R q r) (qp : R q p)
           `{E : Equational A R} `{S : Symmetric A R} : R p r :=
  @_step_sym_eqv A R E p q r qr qp S.

Notation "'begin' pq"    := (begin_  pq) (at level 100).
Notation "'forward'  pq" := (begin_  pq) (at level 100).
Notation "'backward' qp" := (beginr_ qp) (at level 100).

Notation "p ∎" := (final p) (at level 98).

Notation "p ≡⟨⟨ pq ⟩⟩ qr" := (step_eqv p qr pq)
  (at level 99, right associativity).

Notation "p ≡⟨ pq ⟩ qr"  :=
  (step_eqv p qr ltac:(first [ now rewrite pq
                             | now apply pq
                             | now rewrite <- pq ]))
  (at level 99, right associativity).

Notation "p ≡1⟨ pq ⟩ qr"  :=
  (step_eqv p qr ltac:(first [ now rewrite pq at 1
                             | now apply pq
                             | now rewrite <- pq at 1 ]))
  (at level 99, right associativity).

Notation "p ≡2⟨ pq ⟩ qr"  :=
  (step_eqv p qr ltac:(first [ now rewrite pq at 2
                             | now apply pq
                             | now rewrite <- pq at 2 ]))
  (at level 99, right associativity).

Notation "p ≡⟨⟩ pq" := (begin_ (p:=p) ltac:(now simpl pq))
  (at level 99, right associativity).

Notation "p ≡˘⟨⟨ qp ⟩⟩ qr" := (step_sym_eqv p qr qp)
  (at level 99, right associativity).

Notation "p ≡˘⟨ qp ⟩ qr" :=
  (step_sym_eqv p qr ltac:(first [ now rewrite qp
                                 | now apply qp
                                 | now rewrite <- qp ]))
  (at level 99, right associativity).

Notation "p ≡˘1⟨ qp ⟩ qr" :=
  (step_sym_eqv p qr ltac:(first [ now rewrite qp at 1
                                 | now apply qp
                                 | now rewrite <- qp at 1 ]))
  (at level 99, right associativity).

Notation "p ≡˘2⟨ qp ⟩ qr" :=
  (step_sym_eqv p qr ltac:(first [ now rewrite qp at 2
                                 | now apply qp
                                 | now rewrite <- qp at 2 ]))
  (at level 99, right associativity).

Notation "p ⇒⟨⟨ pq ⟩⟩ qr"  := (step_eqv p qr pq)
  (at level 99, right associativity).

Notation "p ⇒⟨ pq ⟩ qr"  :=
  (step_eqv p qr ltac:(first [ now rewrite pq
                             | now apply pq
                             | now rewrite <- pq ]))
  (at level 99, right associativity).

Notation "p ⇒1⟨ pq ⟩ qr"  :=
  (step_eqv p qr ltac:(first [ now rewrite pq at 1
                             | now rewrite <- pq at 1 ]))
  (at level 99, right associativity).

Notation "p ⇒2⟨ pq ⟩ qr"  :=
  (step_eqv p qr ltac:(first [ now rewrite pq at 2
                             | now rewrite <- pq at 2 ]))
  (at level 99, right associativity).

Notation "r ⇐⟨⟨ qr ⟩⟩ pq"  := (step_eqv_r r pq qr)
  (at level 99, right associativity).

Notation "r ⇐⟨ qr ⟩ pq"  :=
  (step_eqv_r r pq ltac:(first [ now rewrite qr
                               | now apply qr
                               | now rewrite <- qr ]))
  (at level 99, right associativity).

Notation "r ⇐1⟨ qr ⟩ pq"  :=
  (step_eqv_r r pq ltac:(first [ now rewrite qr at 1
                               | now rewrite <- qr at 1 ]))
  (at level 99, right associativity).

Notation "r ⇐2⟨ qr ⟩ pq"  :=
  (step_eqv_r r pq ltac:(first [ now rewrite qr at 2
                               | now rewrite <- qr at 2 ]))
  (at level 99, right associativity).

Program Instance eq_Equational {A : Type} : Equational (A:=A) eq.

(* A very brief example. *)
Goal forall m n o, m + (n + o) = (m + n) + o.
Proof.
  intros.
  induction m; auto.
  refine (
    begin
      S m + (n + o)
    ≡⟨ PeanoNat.Nat.add_succ_l ⟩
      S (m + (n + o))
    (* ≡⟨ IHm ⟩ *)
    ≡⟨⟨ ltac:(now rewrite IHm) ⟩⟩
      S (m + n + o)
    ≡⟨⟩
      S (m + n + o)
    ≡⟨ PeanoNat.Nat.add_succ_l ⟩
      S m + n + o
    ∎
  ).
Qed.
