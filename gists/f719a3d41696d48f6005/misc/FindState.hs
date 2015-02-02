{-# LANGUAGE Arrows #-}

module FindState where

-- Minimum to work with arrows:
import Control.Category
import Control.Arrow
import Control.Monad

import Shelly
import qualified Data.Text.Lazy as T
import Filesystem.Path (filename)

import Prelude hiding ((.), id, FilePath)
default (T.Text)

data FindArrow a b =
  FindA {
    callsStat     :: Bool,
    readsMembers  :: Bool,
    runStateArrow :: a -> b
  }

instance Category FindArrow where
  id = FindA False False id
  FindA stat2 memb2 f2 . FindA stat1 memb1 f1 =
    FindA (stat1 || stat2) (memb1 || memb2) $ f2 . f1

instance Arrow FindArrow where
  arr f = FindA False False f
  first (FindA stat memb f) = FindA stat memb $ \(a, c) -> (f a, c)

isDirectory :: FindArrow FilePath (Sh Bool)
isDirectory = FindA True False $ test_d

foo :: FindArrow FilePath (Sh Bool)
foo = proc path -> do
  dir <- isDirectory -< path
  returnA -< dir

bar :: FindArrow FilePath (Sh Bool)
bar = proc path -> do
  returnA -< return $ filename path == (fromText . T.pack $ ".git")

findWhenA :: FindArrow FilePath (Sh Bool) -> FilePath -> Sh [FilePath]
findWhenA = undefined

main :: IO ()
main = do
  print $ callsStat foo
  print $ callsStat bar
  files <- shelly $ findWhenA bar (fromText . T.pack $ "/tmp")
  print files
