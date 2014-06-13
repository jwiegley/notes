Definition fmap {f : Type -> Type} {X Y : Type} (k : X -> Y) : (f X -> f Y) :=
  admit.

Definition lift_yoneda {f : Type -> Type} {X : Type} (a : f X) : Yoneda f X :=
  Y (fun k => fmap k a).
