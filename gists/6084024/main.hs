{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Applicative
import           Control.Exception
import           Control.Monad
import qualified Data.ByteString as B
import           Data.Conduit
import           Data.Conduit.Filesystem
import qualified Data.Conduit.List as CL
import           Data.List
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           Filesystem.Path.CurrentOS
import qualified Prelude
import           Prelude hiding (FilePath)

main :: IO ()
main = preludeStyle "cybersource.h"

conduitStyle :: FilePath -> IO ()
conduitStyle path = do
    ls <- T.lines . T.decodeUtf8 . B.concat
        <$> runResourceT (sourceFile path $$ CL.consume)
    case find ("WS-Header" `T.isInfixOf`) ls of
        Just _  -> return ()
        Nothing ->
            let Just idx = findIndex (" Import " `T.isInfixOf`) ls
            in runResourceT $
                (yield $ T.encodeUtf8 . T.unlines
                       $ take (idx + 3) ls
                      ++ ["#import \"WS-Header.h\""]
                      ++ drop (idx + 3) ls) $$ sinkFile path

preludeStyle :: Prelude.FilePath -> IO ()
preludeStyle path = do
    ls <- lines <$> readFile path
    void $ evaluate (length ls)
    case find ("WS-Header" `isInfixOf`) ls of
        Just _  -> return ()
        Nothing ->
            let Just idx = findIndex (" Import " `isInfixOf`) ls
            in writeFile path
                $ unlines
                $ take (idx + 2) ls
               ++ ["#import \"WS-Header.h\""]
               ++ drop (idx + 2) ls
