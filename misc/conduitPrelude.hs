{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import           Control.Applicative
import           Control.Exception
import           Control.Monad hiding (forM)
import           Control.Monad.IO.Class
import qualified Data.ByteString as B
import           Data.Conduit
import           Data.Conduit.Filesystem
import qualified Data.Conduit.List as CL
import qualified Data.Conduit.Text as CT
import           Data.Foldable hiding (find)
import           Data.List
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           Data.Traversable
import           Data.Void
import           Filesystem.Path.CurrentOS
import qualified Prelude
import           Prelude hiding (FilePath)

conduitStyle :: FilePath -> IO ()
conduitStyle path = do
    ls <- T.lines . T.decodeUtf8 . B.concat
        <$> runResourceT (sourceFile path $$ CL.consume)
    case find ("WS-Header" `T.isInfixOf`) ls of
        Just _  -> return ()
        Nothing ->
            let Just idx = findIndex (" Import " `T.isInfixOf`) ls
            in runResourceT $
                yield (T.encodeUtf8 . T.unlines
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


main :: IO ()
main = do
    runPipe $ forP (yield (1 :: Int) >> yield 2) $ liftIO . print
    runPipe $ forP (each [1..5]) $ liftIO . print
    runPipeR $
        sourceFile "/Volumes/Data/Home/Dropbox/Notes/conduitPrelude.hs"
            >-> CL.isolate 10
            >-> CT.decode CT.utf8
            >-> CT.lines
            >-> CL.isolate 5
            >-> CL.mapM_ (liftIO . print)
