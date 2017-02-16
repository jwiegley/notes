{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Lens.Mutable where

import Control.Concurrent.MVar
import Control.Concurrent.STM
import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.STM.Class
import Control.Monad.ST.Safe
import Data.IORef
import Data.STRef

class Mutable m (s :: * -> *) where
    withMutable :: s a -> (a -> a) -> m ()

instance MonadIO m => Mutable m IORef where
    withMutable = (liftIO .) . modifyIORef

instance MonadIO m => Mutable m MVar where
    withMutable v f = liftIO $ modifyMVar_ v (return . f)

instance Mutable (ST s) (STRef s) where
    withMutable = modifySTRef

instance MonadSTM m => Mutable m TVar where
    withMutable = (liftSTM .) . modifyTVar

instance MonadSTM m => Mutable m TMVar where
    withMutable tmv f = liftSTM $ putTMVar tmv . f =<< takeTMVar tmv

-- | This is an example lens operator for acting on any type of mutable state
--   kept in a variable, rather than in an enclosing State monad.  The idea is
--   to prefix @ before all of the state operators in Control.Lens.
(@+=) :: (Mutable m v, Num a) => ASetter' s a -> a -> v s -> m ()
l @+= arg = withMutable ?? (l +~ arg)

main :: IO ()
main = do
    ior <- newIORef ((10,20) :: (Int, Int))
    mv  <- newMVar ((10,20) :: (Int, Int))
    tv  <- newTVarIO ((10,20) :: (Int, Int))
    tmv <- newTMVarIO ((10,20) :: (Int, Int))

    ior & _2 @+= 5
    mv  & _2 @+= 5
    tv  & _2 @+= 5
    tmv & _2 @+= 5

    print =<< readIORef ior
    print =<< takeMVar mv
    print =<< atomically (readTVar tv)
    print =<< atomically (readTMVar tmv)

    print $ runST $ do
        st <- newSTRef ((10,20) :: (Int, Int))
        st & _2 @+= 5
        readSTRef st
