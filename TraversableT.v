Require Import Hask.Prelude.
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.

Generalizable All Variables.

Include MonadLaws.

Require Import FunctionalExtensionality.

Definition TraversableT (t m : Type -> Type) (a : Type) := m (t a).

Instance TraversableT_Functor `{Functor t} `{Functor m} :
  Functor (TraversableT t m) := {
  fmap := fun _ _ => @fmap m _ _ _ \o @fmap t _ _ _
}.

Program Instance TraversableT_FunctorLaws `{FunctorLaws t} `{FunctorLaws m} :
  FunctorLaws (TraversableT t m).
Obligation 1.
  by rewrite 2!fmap_id_ext.
Qed.
Obligation 2.
  move=> x.
  rewrite /funcomp.
  rewrite fmap_comp_x.
  f_equal.
  extensionality y.
  by rewrite fmap_comp_x.
Qed.

Instance TraversableT_Applicative `{Applicative t} `{Applicative m} :
  Applicative (TraversableT t m) := {
  pure := fun _ => @pure m _ _ \o @pure t _ _;
  ap   := fun _ _ => liftA2 (@ap m _ _ _)
}.

Program Instance TraversableT_ApplicativeLaws
  `{ApplicativeLaws t} `{ApplicativeLaws m} :
  ApplicativeLaws (TraversableT t m).
Obligation 1.
  move=> x /=.
  by rewrite fmap_pure_x !ap_id_ext.
Qed.
Obligation 2.
  rewrite -ap_comp -!ap_fmap; f_equal.
  rewrite !ap_fmap.
Admitted.
Obligation 3.
  by rewrite !fmap_id_ext !fmap_pure_x !ap_homo.
Qed.
Obligation 4.
  rewrite !fmap_id_ext !fmap_pure_x.
  rewrite ap_interchange.
  rewrite !ap_fmap fmap_comp_x -!ap_fmap.
  f_equal; f_equal.
  extensionality z.
  by rewrite -ap_interchange.
Qed.
Obligation 5.
  move=> x /=.
  rewrite !fmap_id_ext !fmap_pure_x.
  rewrite !ap_fmap.
  f_equal.
  extensionality z.
  by rewrite ap_fmap.
Qed.

instance (Monad t, Traversable t, Monad m) => Monad (TraversableT t m) where
    return = TraversableT . pure . pure
    x >>= f = TraversableT $ do
        x' <- runTraversableT x
        let y = runTraversableT . f <$> x'
        join <$> sequence y

instance Applicative t => MonadTrans (TraversableT t) where
    lift = TraversableT . fmap pure

instance (Monad t, Traversable t, MonadIO m) => MonadIO (TraversableT t m) where
    liftIO = TraversableT . fmap pure . liftIO

instance (Traversable t, MonadError e t, Monad m) => MonadError e (TraversableT t m) where
    throwError = TraversableT . return . throwError
    catchError x f = TraversableT $ do
        x' <- runTraversableT x
        let y = sequence $ fmap pure x' `catchError` \e -> pure (f e)
        join <$> runTraversableT y

instance (Alternative t, Traversable t, Monad m) => Alternative (TraversableT t m) where
    empty = TraversableT $ pure empty
    x <|> y = TraversableT $ do
        x' <- runTraversableT x
        let c = sequence $ (return . pure <$> x') <|> pure (runTraversableT y)
        -- c :: m (t (t a))
        -- TODO: is asum okay and not join?
        -- join <$> c
        asum <$> c

instance (MonadPlus t, Traversable t, Monad m) => MonadPlus (TraversableT t m) where
    mzero = empty
    mplus = (<|>)

instance (Foldable t, Foldable m) => Foldable (TraversableT t m) where
    foldMap f (TraversableT x) = foldMap (foldMap f) x

instance (Traversable t, Traversable m) => Traversable (TraversableT t m) where
    traverse f (TraversableT x) = TraversableT <$> traverse (traverse f) x

traversable :: Applicative m => t a -> TraversableT t m a
traversable = TraversableT . pure

