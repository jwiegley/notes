{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (when)
import Control.Monad.IO.Class
import Data.ByteString
import Data.Conduit
import Data.Conduit.Binary hiding (sourceFile)
import Data.Conduit.Filesystem
import Data.Conduit.List as CL
import Data.Function
import Filesystem
import Prelude hiding (catch, lines)
import System.IO

main :: IO ()
main = runResourceT $
    traverse False "/Users/johnw/Projects" $$ fix $ \loop -> do
        mfname <- await
        case mfname of
            Just fname -> do
                exists <- liftIO $ isFile fname
                when exists $
                    sourceFile fname
                        $= lines
                        $= CL.filter ("cout" `Data.ByteString.isInfixOf`)
                        $$ sinkHandle stdout
                loop
            Nothing -> return ()
