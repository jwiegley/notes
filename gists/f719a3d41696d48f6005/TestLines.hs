{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Control.Foldl as L
import           Control.Lens
import           Data.Text as T
import qualified Pipes.Group as P
import qualified Pipes.Prelude as P
import           Pipes.Safe
import qualified Pipes.Text as Text
import qualified Pipes.Text.IO as Text
import           System.Environment

main :: IO ()
main = do
    [path] <- getArgs
    b <- runSafeT $
        P.any ("> " `T.isPrefixOf`)
              (L.purely P.folds L.mconcat
                        (Text.readFile path ^. Text.lines))
    print b
