Theorem fmap_compose
  : forall (F : Type -> Type) (G : Type -> Type)
      `{f_dict : Functor F} `{g_dict : Functor G}
      {X Y} (f : X -> Y),
  (@fmap F f_dict (G X) (G Y) (@fmap G g_dict X Y f)) =
  (@fmap (fun X => F (G X)) _ X Y f).
Proof.
  intros; simpl.
  unfold compose_fmap, compose.
  reflexivity.
Qed.
