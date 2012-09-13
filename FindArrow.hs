{-# LANGUAGE Arrows #-}
{-# LANGUAGE OverloadedStrings #-}

module FindState where

-- Minimum to work with arrows:
import Control.Category
import Control.Arrow
import Control.Monad
import Data.Monoid

import Prelude hiding ((.), id, FilePath)
import Data.Text.Lazy (Text)
import Shelly
import Filesystem.Path (filename)
import Filesystem (isDirectory, listDirectory)
import Filesystem.Path.CurrentOS (FilePath, encodeString, relative)
import System.PosixCompat.Files( getSymbolicLinkStatus, isSymbolicLink )

import Data.Text.Lazy

data FindArrow a b =
  FindA {
    callsStat        :: Bool,
    readsMembers     :: Bool,
    traverseSymlinks :: Bool,
    crossFilesystems :: Bool,
    runFindArrow     :: a -> b
  }

instance Category FindArrow where
  id = FindA False False False False id
  FindA stat2 memb2 sym2 fsys2 f2 . FindA stat1 memb1 sym1 fsys1 f1 =
    FindA (stat1 || stat2)
          (memb1 || memb2)
          (sym1  || sym2)
          (fsys1 || fsys2) $ f2 . f1

instance Arrow FindArrow where
  arr f = FindA False False False False f
  first (FindA stat memb syms fsys f) =
    FindA stat memb syms fsys $ \(a, c) -> (f a, c)

findWhenA :: FindArrow FilePath (Sh Bool) -> FilePath -> Sh [FilePath]
findWhenA = findDirFilterWhenA $ arr (const $ return True)

-- | similar 'findWhen', but also filter out directories
-- Alternatively, similar to 'findDirFilter', but also filter out files
-- Filtering out directories makes the find much more efficient
findDirFilterWhenA :: FindArrow FilePath (Sh Bool) -- ^ directory filter
                   -> FindArrow FilePath (Sh Bool) -- ^ file filter
                   -> FilePath -- ^ directory
                   -> Sh [FilePath]
findDirFilterWhenA dirFilt fileFilter = findFoldDirFilterA filterIt [] dirFilt
  where
    filterIt paths fp = do
      yes <- runFindArrow fileFilter fp
      return $ if yes then paths ++ [fp] else paths

lsRelAbs :: FilePath -> Sh ([FilePath], [FilePath])
lsRelAbs f = absPath f >>= \fp -> do
  filt <- if not (relative f) then return return
             else do
               -- jww (2012-08-20): No access to this function
               -- wd <- gets sDirectory
               wd <- return . fromText $ "foo"
               return (relativeTo wd)
  absolute <- liftIO $ listDirectory fp
  relativized <- mapM filt absolute
  return (relativized, absolute)

  where gets f = f <$> get

-- | like 'findDirFilterWhen' but use a folding function rather than a filter
-- The most general finder: you likely want a more specific one
findFoldDirFilterA :: (a -> FilePath -> Sh a)
                   -> a
                   -> FindArrow FilePath (Sh Bool)
                   -> FilePath
                   -> Sh a
findFoldDirFilterA folder startValue dirFilter dir = do
  absDir <- absPath dir
  trace ("find " `mappend` toTextIgnore absDir)
  filt <- runFindArrow dirFilter absDir
  if not filt then return startValue
    -- use possible relative path, not absolute so that listing will remain relative
    else do
      (rPaths, aPaths) <- lsRelAbs dir 
      foldM traverse startValue (Prelude.zip rPaths aPaths)
  where
    traverse acc (relativePath, absolutePath) = do
      -- optimization: don't use Shelly API since our path is already good
      isDir <- liftIO $ isDirectory absolutePath
      sym   <- if traverseSymlinks dirFilter
               then return False
               else liftIO $ fmap isSymbolicLink
                           $ getSymbolicLinkStatus (unpack (toTextIgnore absolutePath))
      newAcc <- folder acc relativePath
      if isDir && not sym
        then findFold folder newAcc relativePath
        else return newAcc

isDirectoryA :: FindArrow FilePath (Sh Bool)
isDirectoryA = FindA True False False False $ test_d

foo :: FindArrow FilePath (Sh Bool)
foo = proc path -> do
  dir <- isDirectoryA -< path
  returnA -< dir

bar :: FindArrow FilePath (Sh Bool)
bar = proc path -> do
  returnA -< return $ filename path == ".git"

main :: IO ()
main = do
  print $ callsStat foo
  print $ callsStat bar
  files <- shelly $ findWhenA bar "/Users/johnw/Projects"
  print files
