Ltac zoom T :=
  let Ty := type of T in
  let U := fresh "U" in evar (U : Ty);
  let H := fresh "H" in assert (T = U) as H;
    [ subst U | setoid_rewrite H; clear H; unfold U; clear U ].
