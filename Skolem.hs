{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Skolem where

import Data.Functor.Identity

newtype Foo s a = Foo { getFoo :: Identity a } deriving Monad

runFoo :: (forall s. Foo s a) -> a
runFoo (Foo f) = runIdentity f

data Handle s = Handle { getHandle :: Int }

makeHandle :: Int -> Foo s (Handle s)
makeHandle = return . Handle

readHandle :: Handle s -> Foo s Int
readHandle = return . getHandle

main :: IO ()
main = do
    -- first block
    let x = runFoo $ makeHandle 100
    -- second block
    let y = runFoo $ readHandle x
    print y
