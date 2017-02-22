Module Ptr_as_OT <: UsualOrderedType.
  Definition t:=Ptr Word.
  Definition eq:=eqPtr (A:=Word).

  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := ltPtr (A:=Word).
  Definition lt_trans := N.lt_trans.
  Definition lt_not_eq := N.lt_neq.

  Definition compare x y : Compare (ltPtr (A:=Word)) (eqPtr (A:=Word)) x y.
  Proof.
  case_eq (x ?= y)%N; intro.
  - apply EQ. now apply N.compare_eq.
  - apply LT. assumption.
  - apply GT. now apply N.gt_lt.
  Defined.

  Definition eq_dec := eqdecPtr (A:=Word).
End Ptr_as_OT.
