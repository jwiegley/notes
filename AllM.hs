{-# LANGUAGE OverloadedStrings #-}

module AllM where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Maybe
import Control.Monad.Loops
import Data.Maybe
import Data.Monoid

allM :: [IO Bool] -> IO Bool
allM [] = return True
allM (x:xs) = do
    y <- x
    if y then allM xs else return False

allM' :: [IO Bool] -> IO Bool
allM' xs = firstM id xs

main :: IO ()
main = undefined
