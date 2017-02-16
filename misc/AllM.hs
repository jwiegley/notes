{-# LANGUAGE OverloadedStrings #-}

module AllM where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Maybe
import Control.Monad.Loops hiding (allM)
import Data.Maybe
import Data.Monoid
import Control.Concurrent.STM (atomically)
import Control.Lens (makeLenses)

data Foo = Foo | Bar

allM :: [IO Bool] -> IO Bool
allM [] = return True
allMx (x:xs) = do
    y <- x
    if y then allM xs else return False
    atomically $ return ()
    untilM undefined undefined

main :: IO ()
main = undefined
