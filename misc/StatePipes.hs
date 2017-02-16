{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module StatePipes where

import Control.Applicative
import Control.Monad.Trans.Cont
import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Data.Functor.Identity
import Debug.Trace

newtype PipeT r s m a = PipeT
    { runPipeT :: ContT r (StateT (PipeT r s m r) m) a }
    deriving (Functor, Applicative, Monad)

putP :: Monad m => s -> PipeT r s m ()
putP s = PipeT $ do
    k <- lift get
    runPipeT (fst k s)

getP :: Monad m => PipeT r s m s
getP = PipeT $ do
    h <- lift get
    callCC $ \k -> do
        lift $ put (fmap PipeT k, snd h)
        runPipeT (snd h)

foo :: PipeT r Int Identity ()
foo = loop 10
  where
    loop 0 = return ()
    loop n = do
        putP n
        loop (n-1)

bar :: PipeT r Int Identity Int
bar = do
    x <- getP
    traceM $ "x = " ++ show x
    y <- getP
    traceM $ "y = " ++ show x
    z <- getP
    traceM $ "z = " ++ show x
    return $ x + y + z

main :: IO ()
main = do
    print $ runIdentity
          $ flip evalStateT (const foo, return 0)
          $ flip runContT return
          $ runPipeT
          $ bar
