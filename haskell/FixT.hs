module Control.Monad.Trans.Fix where

newtype Effect f m = Effect { getEffect :: m (FixT f m) }

data FixT f m = FixT { unFixT :: f (Effect f m) }
