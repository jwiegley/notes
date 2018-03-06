Require Import Coq.Program.Tactics.
Require Import Coq.Program.Program.
Require Import Coq.Bool.Sumbool.
Require Import Omega.

Open Scope bool_scope.
Open Scope Z_scope.

Program Definition g (i: Z) (h: (Z.gtb i 0 = true)) : {holds: bool | (holds = true)} :=
  Z.geb i (-1).
Next Obligation.
  apply Z.geb_le.
  apply Z.gtb_lt in h.
  omega.
Qed.

Program Definition f (i: Z) (h: (Z.geb i 0 = true)) : bool :=
  Z.gtb i 0.

Lemma impl {i j} : Z.gtb i j = true -> Z.geb i j = true.
Proof.
  intros.
  apply Z.geb_le.
  apply Z.gtb_lt in H.
  omega.
Qed.

Program Definition h (i: Z) (h: match sumbool_of_bool (Z.gtb i 0) with
                                | left H => f (Z.sub i 1) (impl H)
                                | right _ => false
                                end = true) :
  {res: Z | g (Z.add i 1) _ = true } :=
  Z.add i 1.
Next Obligation.
  clear Heq_anonymous.
  apply Z.gtb_lt in H.
  assert (i >=? 0 = true).
    apply Z.geb_le; abstract omega.
  assert (i - 1 >=? 0 = true).
    apply Z.geb_le; abstract omega.
  now rewrite H0, H1.
Defined.
Next Obligation.
  destruct (dec (i >? 0)); simpl.
    clear h.
    apply Z.gtb_lt in e.
    apply Z.gtb_lt; abstract omega.
  discriminate.
Defined.
Next Obligation.
  unfold g.
  apply eq_exist_uncurried.
  assert ((i + 1 >=? -1) = true).
    destruct (dec (i >? 0)); simpl.
      clear h.
      apply Z.gtb_lt in e.
      apply Z.geb_le; omega.
    discriminate.
  exists H.
  unfold h_obligation_3. simpl.
  unfold eq_rect.
  apply Eqdep_dec.UIP_dec.
  apply Bool.bool_dec.
Qed.