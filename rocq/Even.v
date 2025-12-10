Generalizable All Variables.

Definition plus (n m : nat) : nat :=
  match n with
    | O => m
    | S x => S (plus x m)
  end.

Fixpoint even (n : nat) : Prop :=
  match n with
    | O => True
    | S 0 => False
    | S (S x) => even x
  end.

Lemma even_0 : even 0.
Proof.
  constructor.
Qed.

Lemma even_SS : forall n, even n -> even (S (S n)).
Proof.
  induction n; intros.
    constructor.
  assumption.
Qed.

Fixpoint plus_even_is_even (n m : nat) {struct n} :
  even n -> even m -> even (n + m).
Proof.
  destruct n; intros.
    assumption.
  destruct n.
    inversion H.
  rewrite plus_Sn_m; rewrite plus_Sn_m.
  apply plus_even_is_even; assumption.
Qed.

Inductive Even : nat -> Set :=
  | Ev_0    : Even 0
  | Ev_SS n : Even n -> Even (S (S n)).

Fixpoint even_plus `(en : Even n) `(em : Even m) : Even (n + m) :=
  match en in Even n' return Even (n' + m) with
  | Ev_0 =>
      match em in Even n' return Even (0 + n') with
      | Ev_0 => Ev_0
      | Ev_SS n' em' => Ev_SS _ em'
      end
  | Ev_SS n' en' => Ev_SS _ (even_plus en' em)
  end.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

Extraction Even.
Extraction even_plus.

(*

data Even = Ev_0 | Ev_SS Nat Even

even_plus :: Nat -> Even -> Nat -> Even -> Even
even_plus n en m em =
  case en of {
   Ev_0 -> em;
   Ev_SS n' en' -> Ev_SS (plus n' m) (even_plus n' en' m em)}

*)