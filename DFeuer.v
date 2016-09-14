Definition star_angle `{Applicative f} {a b} : f a -> f b -> f b :=
  liftA2 (const id).

Infix "*>" := star_angle (at level 42).

Import ApplicativeLaws.

Theorem dfeuer_20160914 (a b c : Type) `{ApplicativeLaws f} :
  forall (k : a -> b) (u : f a) (v : f c),
    fmap k u *> v = u *> v.
Proof.
  unfold star_angle, const, id, liftA2; intros; simpl.
  rewrite fmap_comp_x.
  reflexivity.
Qed.
