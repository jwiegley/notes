{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module EState where

import Control.Arrow
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State

newtype AutoProc m a b
  = AutoProc { runAutoProc :: a -> m (Maybe b, AutoProc m a b) }

newtype EState a = EState { runEState :: forall s. s -> (a, s) }

instance Functor EState where
  fmap f (EState m) = EState (\s -> let (a, s') = m s in (f a, s'))

instance Applicative EState where
  pure x = EState (x,)
  EState f <*> EState x = EState $ \s ->
    let (f', s')  = f s
        (x', s'') = x s'
    in (f' x', s'')

instance Monad EState where
  return = pure
  EState m >>= f = EState $ \s ->
    let (x, s') = m s in runEState (f x) s'

newtype EStateT m a = EStateT { runEStateT :: forall s. s -> m (a, s) }

instance Functor m => Functor (EStateT m) where
  fmap f (EStateT m) = EStateT (\s -> do first f <$> m s)

instance Monad m => Applicative (EStateT m) where
  pure x = EStateT $ \s -> pure (x, s)
  EStateT f <*> EStateT x = EStateT $ \s -> do
    (f', s') <- f s
    fmap (first f') (x s')

instance Monad m => Monad (EStateT m) where
  return = pure
  EStateT m >>= f = EStateT $ \s -> do
    (x, s') <- m s
    runEStateT (f x) s'

type AutoProc' m a b = a -> MaybeT EState b

newtype PState s a = PState { runPState :: s -> (Maybe a, s) }

instance Functor (PState s) where
  fmap f (PState m) = PState (\s -> let (a, s') = m s in (f <$> a, s'))

instance Applicative (PState s) where
  pure x = PState (Just x,)
  PState f <*> PState x = PState $ \s ->
    let (mf, s') = f s
        (mx, s'') = x s'
    in (mf <*> mx, s'')

instance Monad (PState s) where
  return = pure
  PState m >>= f = PState $ \s ->
    let (mres, s') = m s in
    case mres of
      Nothing -> (Nothing, s')
      Just x  -> runPState (f x) s'

toAuto :: Functor m => (forall s. a -> MaybeT (StateT s m) b) -> AutoProc m a b
toAuto k = AutoProc $ go ()
  where
  go s a = second (AutoProc . go) <$> runStateT (runMaybeT (k a)) s

fromAuto :: Functor m => AutoProc m a b -> (forall s. (a -> MaybeT (StateT s m) b) -> r) -> r
fromAuto (AutoProc k) cont = cont $ \a -> MaybeT $ StateT $ \_ ->
  second runAutoProc <$> k a
