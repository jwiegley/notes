Require Import Coq.Program.Tactics.
Require Import Coq.Program.Program.
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

Program Definition h (i: Z) (h: match Z.gtb i 0 with
                                | true => f (Z.sub i 1) _
                                | false => false
                                end = true) :
  {res: Z | g (Z.add i 1) _ = true } :=
  Z.add i 1.
