{-# LANGUAGE RankNTypes #-}

module ContFree where

import Control.Monad.Free
import Control.Monad.Trans.Cont

to :: Monad f => Free f a -> (forall r. ContT r f a)
to (Pure x) = ContT ($ x)
to (Free f) = ContT $ \k -> f >>= \f' -> runContT (to f') k

from :: Applicative f => (forall r. ContT r f a) -> Free f a
from (ContT k) = Free (k $ fmap Pure . pure)
