module STExample where

import Control.Monad
import Control.Monad.ST
import Data.STRef

fib n = runST $ do
    var_a <- newSTRef 0
    var_b <- newSTRef 1
    replicateM_ (n-1) $ do
        a <- readSTRef var_a
        b <- readSTRef var_b
        writeSTRef var_a b
        writeSTRef var_b (a+b)
    readSTRef var_a
