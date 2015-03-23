Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrfun.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrnat.
Require Export Ssreflect.fintype.

Inductive BigType :=
  | A
  | B
  | C.

Inductive true_xor_false (x : BigType) (f : BigType -> bool) :
  bool -> bool -> Set :=
  | EqNotNeq : f x -> true_xor_false x f true false
  | NeqNotEq : ~~ f x -> true_xor_false x f false true.

Lemma matchP (x : BigType) (f : BigType -> bool) :
  true_xor_false x f (f x) (~~ f x).
Proof.
  case E: (f x).
    by constructor.
  constructor.
  by rewrite E.
Qed.

Definition is_B (x : BigType) : bool :=
  match x with
    | A => false
    | B => true
    | C => false
  end.

Lemma check_B (x : BigType) : is_B x = true.
Proof.
  case: (matchP x is_B) => H.
    reflexivity.
  (* of course we can't prove that every x is a B! *)
  admit.
Qed.
