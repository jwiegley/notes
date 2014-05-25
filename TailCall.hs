{-# LANGUAGE OverloadedStrings #-}

module TailCall where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid
import Data.Time

tco :: [Int] -> IO ()
tco [] = return ()
tco (x:xs) = tco xs

nonTco :: [Int] -> IO ()
nonTco [] = return ()
nonTco (x:xs) = nonTco xs >> return ()

main :: IO ()
main = do
    start <- getCurrentTime
    tco (replicate 10000000 1)
    end <- getCurrentTime
    putStrLn (show (diffUTCTime end start))

    start <- getCurrentTime
    nonTco (replicate 10000000 1)
    end <- getCurrentTime
    putStrLn (show (diffUTCTime end start))
