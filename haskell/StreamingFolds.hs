{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module StreamingFolds where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Control.Monad.Trans.State
import Data.Void
import Debug.Trace

shift :: ((a -> Cont s r) -> Cont r r) -> Cont r a
shift e = ContT $ \k -> e (lift . k) `runContT` return

reset :: Cont a a -> Cont r a
reset e = return $ e `runCont` id

newtype Pipe i r = Pipe
    { unPipe :: StateT (Maybe (Either (Pipe i (Step i r))
                                     (Cont r (Step i r))))
                      (Cont r) i }

instance Monad (Pipe i)

runPipe :: Pipe r r -> r
runPipe p = runCont (evalStateT (unPipe p) Nothing) id

data Step a b = Done | Step a (Cont b (Step a b))

await :: Pipe o (Maybe o)
await = Pipe $ do
    Just e <- get
    x <- case e of
        Left e'  -> unPipe e' >>= lift . reset
        Right e' -> lift e'
    case x of
        Step y next -> do
            put $ Just (Right next)
            return next
        Done -> do
            put Nothing
            return undefined

yield :: o -> Pipe o (Step o r)
yield o = Pipe $ lift $ shift $ \k -> return $ Step o (k undefined)

(>->) :: Pipe a (Step a r) -> Pipe a r -> Pipe a r
u >-> d = Pipe $ do
    put . Just . Left $ u
    unPipe d

producer :: Pipe Int (Step Int r)
producer = do
    yield 1
    yield 2
    yield 3

consumer :: Pipe Int Int
consumer = do
    x <- await
    trace (show x) $ return ()
    x <- await
    trace (show x) $ return ()
    x <- await
    trace (show x) $ return ()
    x <- await
    trace (show x) $ return ()
    return 10

main :: IO ()
main = print $ runPipe (producer >-> consumer)
