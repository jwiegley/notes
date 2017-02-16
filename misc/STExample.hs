{-# LANGUAGE ScopedTypeVariables #-}

module STExample where

import Control.Monad
import Control.Monad.ST
import Data.STRef
import Prelude hiding (read)

new  = newSTRef
read = readSTRef
(=:) = writeSTRef

fib n = runST $ do
    var_a <- new 0
    var_b <- new 1
    replicateM_ (n-1) $ do
        a <- read var_a
        b <- read var_b
        var_a =: b
        var_b =: (a + b)
    read var_a
