{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Shlevy where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Monoid

withSomeShow :: Bool -> (forall x. Show x => x -> a) -> a
withSomeShow b f = f ()

main :: IO ()
main = undefined
