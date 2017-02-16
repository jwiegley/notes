module Main where

import Data.Function

newtype Fix f = Fix (f (Fix f))

type Test = Fix Maybe

foo :: Test
foo = fix $ Fix . Just

join :: Monad m => m (m a) -> m a
join mx = mx >>= id
