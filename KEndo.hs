{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module KEndo where

import Control.Monad (liftM, join)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer (execWriterT, tell)
import Data.Semigroup.Monad

main :: IO ()
main = do
    actions <- execWriterT $ do
        tell $ Action $ print "Hello"
        lift $ print "Inside writer"
        tell $ Action $ print "Leaving"
        lift $ print "Goodbye"
    getAction actions
