{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main where

import Shelly
import System.IO.Silently
import System.IO (stdout, stderr)
import ClassyPrelude

main = do
    output <- hCapture_ [stdout, stderr] $ do
        putStrLn "This is a test!"
        catchany (void go) (\e -> putStrLn $ "Exception: " ++ show e)
    print "I captured some output"
    print output
  where
    go = shellyNoDir $ do
        echo "Hello, world!"
        run "git" ["version"]
        run "git" ["versionx"]
