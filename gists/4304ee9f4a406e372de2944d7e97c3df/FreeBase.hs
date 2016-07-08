{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module FreeBase where

import Control.Monad.Trans.Control
import Control.Monad.Trans.Free
import Control.Monad.Base

instance (MonadBase b m, Functor f) => MonadBase b (FreeT f m) where
    liftBase = liftBaseDefault

instance (MonadBaseControl b m, Functor f)
         => MonadBaseControl b (FreeT f m) where
    type StM (FreeT f m) a = StM m (FreeF f a (FreeT f m a))
    liftBaseWith f =
        FreeT $ fmap Pure $ liftBaseWith $ \runInBase -> f $ \k ->
            runInBase $ runFreeT k
    restoreM = FreeT . restoreM
