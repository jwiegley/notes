#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Main where

import qualified Data.Text.Lazy as T
import Shelly
import Control.Monad
import System.Environment
import System.Console.CmdArgs
import Prelude hiding (FilePath)

sudo_ com args = run_ "sudo" (com:args)

main :: IO ()
main = shelly $ verbosely $ do
  args <- liftIO getArgs
  sudo_ "ls" $ map T.pack args
