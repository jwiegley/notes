Inductive BigType :=
  | A
  | B
  | C.

Inductive true_xor_false (x : BigType) (f : BigType -> bool) :
  bool -> bool -> Set :=
  | EqNotNeq : f x = true -> true_xor_false x f true false
  | NeqNotEq : negb (f x) = true -> true_xor_false x f false true.

Lemma matchP (x : BigType) (f : BigType -> bool) :
  true_xor_false x f (f x) (negb (f x)).
Proof.
  destruct (f x) eqn:E.
    constructor.
    assumption.
  constructor.
  rewrite E.
  reflexivity.
Qed.

Definition is_B (x : BigType) : bool :=
  match x with
    | A => false
    | B => true
    | C => false
  end.

Lemma check_B (x : BigType) : is_B x = true.
Proof.
  destruct (matchP x is_B) as [Htrue|Hfalse].
    reflexivity.
  (* of course we can't prove that every x is a B! *)
  admit.
Qed.
