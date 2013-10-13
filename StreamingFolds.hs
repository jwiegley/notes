{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module StreamingFolds where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Data.Void
import Debug.Trace

shift :: ((a -> Cont s r) -> Cont r r) -> Cont r a
shift e = ContT $ \k -> e (lift . k) `runContT` return

reset :: Cont a a -> Cont r a
reset e = return $ e `runCont` id

type Pipe i o r = Cont r o

runPipe :: Pipe Void r r -> r
runPipe p = runCont p id

data Step a b = Done | Step a (Cont b (Step a b))

yield :: o -> Pipe i Void (Step o b)
yield o = shift $ \k -> return $ Step o (k undefined)

(>->) :: Pipe Void a a -> (Pipe Void a r -> p) -> p
u >-> d = d (reset u)

producer :: Pipe Void (Step Int r) (Step Int r)
producer = do
    yield 1
    yield 2
    yield 3
    return Done

consumer :: Cont r (Step Int r) -> Pipe Int String r
consumer i = do
    Step x await <- i
    trace (show x) $ return ()
    Step x' await' <- await
    trace (show x') $ return ()
    Step x'' _ <- await'
    trace (show x'') $ return ()
    return "Hello"

main :: IO ()
main = print $ runPipe (producer >-> consumer)
