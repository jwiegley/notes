Require Import Coq.Program.Tactics.
Require Import Coq.Program.Program.
Require Import Coq.Bool.Sumbool.
Require Import Omega.

Open Scope bool_scope.
Open Scope Z_scope.

Ltac Omega :=
  repeat match goal with
  | [ H : (_ >? _) = true |- _ ] => apply Z.gtb_lt in H
  | [ H : (_ >=? _) = true |- _ ] => apply Z.geb_le in H
  | [ |- (_ >? _) = true ] => apply Z.gtb_lt
  | [ |- (_ >=? _) = true ] => apply Z.geb_le
  end; abstract omega.

Program Definition g (i: Z) (h: (Z.gtb i 0 = true)) : {holds: bool | (holds = true)} :=
  Z.geb i (-1).
Next Obligation. Omega. Qed.

Program Definition f (i: Z) (h: (Z.geb i 0 = true)) : bool :=
  Z.gtb i 0.

Lemma impl {i j} : Z.gtb i j = true -> Z.geb i j = true.
Proof. intros; Omega. Qed.

Program Definition h (i: Z) (h: match sumbool_of_bool (Z.gtb i 0) with
                                | left H => f (Z.sub i 1) (impl H)
                                | right _ => false
                                end = true) :
  {res: Z | g (Z.add i 1) _ = true } :=
  Z.add i 1.
Next Obligation.
  clear Heq_anonymous.
  assert (i >=? 0 = true) by Omega.
  assert (i - 1 >=? 0 = true) by Omega.
  now rewrite H0, H1.
Defined.
Next Obligation.
  destruct (dec (i >? 0)); simpl.
    clear h; Omega.
  discriminate.
Defined.
Next Obligation.
  apply eq_exist_uncurried.
  assert ((i + 1 >=? -1) = true).
    destruct (dec (i >? 0)); simpl.
      clear h; Omega.
    discriminate.
  exists H.
  apply Eqdep_dec.UIP_dec, Bool.bool_dec.
Qed.
