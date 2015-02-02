Program Instance Cat_HasInitial : HasInitial Cat := {
    init_obj := Zero;
    init_mor := Init
}.
Obligation 1.
  induction f as [F].
  induction g as [G].
  assert (F = G).
    extensionality e.
    crush.
  replace F with G. subst.
  assert (fmap0 = fmap1).
    extensionality e.
    extensionality f.
    extensionality g.
    crush.
  apply fun_irrelevance.
  assumption.
Qed.
