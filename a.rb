{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Data.String
import qualified System.Environment as SE
import qualified System.Exit        as SX
import qualified System.Process     as SP
import Data.Yaml as Y
import Data.Aeson
import Data.Aeson.TH
import Control.Applicative
-- import Ghc.Generics

data Pointer = Pointer {
 point :: [String]
  } deriving (Show) --, Generic)
deriveJSON defaultOptions ''Pointer

data Pointer2 = Pointer2 {
 point2 :: [String]
  } deriving (Show) --, Generic)

deriveJSON defaultOptions ''Pointer2


readConfig :: IO (Maybe Pointer)
readConfig = do
  results <- Y.decodeFile "points.yml" :: IO (Maybe Pointer)
  return (results)

main = do
    mp <- readConfig
    print mp
