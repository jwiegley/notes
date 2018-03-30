Theorem azip: forall g y z,
  (forall a b, (a -> b) -> g a -> g b) ->
  (forall f x, (forall a b, (a -> b) -> f a -> f b) -> f (g x) -> g (f x))
  -> g y -> g z -> g (y * z)%type.
Proof.
  intros g y z gmap distribute gy gz.
  specialize (distribute (fun x => y * x)%type z).
  simpl in distribute.
  apply distribute; intros; intuition.
Admitted.
