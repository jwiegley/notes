Record Effects (m : Type -> Type) := E {
  getCharEff : m nat;
  putCharEff : nat -> m unit;
  forkIOEff : forall a, m a -> m nat
}.

Arguments getCharEff {m} _.

Definition Free effect a := forall `{Monad m}, effect m -> m a.

Definition IO := Free Effects.

Definition foo : IO nat.
  eapply (@getCharEff _).
  constructor.
  ??.