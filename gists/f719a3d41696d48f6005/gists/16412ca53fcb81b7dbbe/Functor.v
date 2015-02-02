Theorem app_homomorphism_2
  : forall {F : Type -> Type} {app_dict : Applicative F}
      {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
  f <$> eta x <*> eta y = eta (f x y).
Proof.
  intros.
  rewrite <- app_homomorphism.
  rewrite <- app_homomorphism.
  rewrite app_fmap_unit.
  reflexivity.
Qed.

Definition flip {X Y} (x : X) (f : X -> Y) : Y :=
  f x.

Theorem app_flip
  : forall {F : Type -> Type} {app_dict : Applicative F}
      {X Y} (x : F X) (f : X -> Y),
  eta f <*> x = eta flip <*> x <*> eta f.
Proof.
  intros. rewrite app_interchange.
  rewrite <- app_composition.
  rewrite app_fmap_unit.
  rewrite app_fmap_unit.
  rewrite app_homomorphism_2.
  unfold compose.
  rewrite app_fmap_unit. reflexivity.
Qed.
