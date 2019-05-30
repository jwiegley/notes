{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module ComponentQueue where

import Control.Monad.State

-- The interface IFoo

class Monad m => IFoo m where
  foo :: m ()

-- The component Foo provides the interface IFoo

type Lens' a b = forall f. (a -> f a) -> b -> f b

class Has a b where
  hasLens :: Lens' a b

newtype Foo m a = Foo { runFoo :: forall s. (MonadState s m, Has Int s) => m a }

instance Monad (Foo m) => IFoo (Foo m) where
  foo = pure ()

-- The component 'bar' is implemented in terms of IFoo

bar :: forall m s. (IFoo m, MonadState s m, Has Float s) => m ()
bar = pure ()

-- The IQueue interface

class IQueue where
