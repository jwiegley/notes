{-# LANGUAGE OverloadedStrings #-}

module RWSEitherT where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Either
import Control.Monad.Trans.RWS
import Data.Monoid
import Debug.Trace

foo :: RWST r () s (Either ()) Int
foo = do
    trace "foo..1" $ return ()
    return 10

foo' :: RWST r () s (Either ()) Int
foo' = do
    trace "foo'..1" $ return ()
    lift $ Left ()
    trace "foo'..2" $ return ()
    return 20

bar :: EitherT () (RWS r () s) Int
bar = do
    trace "bar..1" $ return ()
    return 10

bar' :: EitherT () (RWS r () s) Int
bar' = do
    trace "bar'..1" $ return ()
    left ()
    trace "bar'..2" $ return ()
    return 20

main :: IO ()
main = do
    print $ runRWST foo () ()
    print $ runRWST foo' () ()
    print $ runRWS (runEitherT bar) () ()
    print $ runRWS (runEitherT bar') () ()
