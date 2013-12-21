#!/usr/bin/env runhaskell

module Main where

import System.Environment (getArgs)
import System.FilePath
import System.Directory
import Control.Monad (forM_, when, unless)
import Data.Char (toLower)
import Data.List (delete)

-- Usage: update <DIRS...> <TARGET-DIR>
--
-- I use this to update from a backup of the Bizcard fileset as follows:
--   cd /mnt/abc-p1-ss-1 ; update fs1 fs2 /mnt/data

main = do 
  args <- getArgs
  forM_ (init args) $ \f -> updateDirectory f (last args)
  putStrLn "Directories updated."

translatePath :: FilePath -> FilePath
translatePath path = dropFileName path </> map toLower (takeFileName path)

updateElement :: FilePath -> FilePath -> IO ()
updateElement source target = do
  isdir <- doesDirectoryExist source
  let dest = translatePath target
  if isdir
    then do exists <- doesDirectoryExist dest
            unless exists $ do
              putStrLn $ "Creating: " ++ dest
              createDirectory dest
            updateDirectory source dest
    else do isfile <- doesFileExist source
            when isfile $ updateFile source dest

removeFilePath :: FilePath -> IO ()
removeFilePath path = do
  fexists <- doesFileExist path
  dexists <- doesDirectoryExist path
  when (fexists || dexists) $ do
    putStrLn $ "Removing: " ++ path
    if fexists
      then removeFile path
      else removeDirectoryRecursive path

updateDirectory :: FilePath -> FilePath -> IO ()
updateDirectory source target = do
  contents <- getDirectoryContents source
  forM_ (delete "." $ delete ".." contents) $ \e ->
    updateElement (source </> e) (target </> e)
    
  tcontents <- getDirectoryContents target
  forM_ (delete "." $ delete ".." tcontents) $ \e -> do
    s_isdir  <- doesDirectoryExist (source </> e)
    s_isfile <- doesFileExist (source </> e)
    unless (s_isdir || s_isfile) $ removeFilePath (target </> e)

updateFile :: FilePath -> FilePath -> IO ()
updateFile source target = do
  exists <- doesFileExist target
  if exists
    then do srctime <- getModificationTime source
            dsttime <- getModificationTime target
            when (srctime > dsttime) $ copy source target
    else copy source target

  where copy a b = do putStrLn $ "Copying: " ++ a ++ " -> " ++ b
                      copyFile a b

-- update.hs ends here
