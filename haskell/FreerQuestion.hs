{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module FreerQuestion where

import Control.Monad.Base
import Control.Monad.Freer
import Control.Monad.Freer.Internal
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.OpenUnion
import Data.OpenUnion.Internal

instance MonadBase m m => MonadBaseControl m (Eff '[m]) where
    type StM (Eff '[m]) a = a
    liftBaseWith f = sendM (f runM)
    restoreM = return

instance (Data.OpenUnion.LastMember x r,
          MonadBase m x,
          MonadBaseControl m (Eff r))
      => MonadBaseControl m (Eff (Reader e ': r)) where
    type StM (Eff (Reader e ': r)) a = StM (Eff r) a
    liftBaseWith f = do
        e <- ask
        raise $ liftBaseWith $ \runInBase ->
            f $ \k -> runInBase (runReader e k)
    restoreM = raise . restoreM

instance (Data.OpenUnion.LastMember x (r ': s),
          MonadBase m x,
          Data.OpenUnion.Internal.FindElem x s (State e : r : s),
          MonadBaseControl m (Eff (r ': s)))
      => MonadBaseControl m (Eff (State e ': r : s)) where
    type StM (Eff (State e ': r ': s)) a = StM (Eff (r ': s)) (a, e)
    liftBaseWith f = do
        e <- get @e
        raise $ liftBaseWith $ \runInBase ->
            f $ \k -> runInBase (runState e k)
    restoreM x = do
        (a, e :: e) <- raise (restoreM x)
        put e
        return a

-- foo :: (Member (Reader Int) r, Member (State Int) r, Member IO r) => Eff r ()
-- foo = do
--     r <- ask @Int
--     put @Int 1000
--     () <- control $ \runInBase -> do
--         putStrLn "In IO!"
--         s' <- runInBase $ do
--             put @Int 2000
--         putStrLn "Back in IO!"
--         return s'
--     s <- get @Int
--     send @IO $ print s

-- main :: IO ()
-- main = runM . evalState (200 :: Int) . runReader (10 :: Int) $ foo
