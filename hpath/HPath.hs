module HPath where

import Control.Applicative
import Control.Lens
import Filesystem

-- | Monadic filtering for lens
--
-- >>> "/tmp" ^!! act listDirectory.folded.files
filteredM f = act  (\x -> (,) <$> pure x <*> f x).filtered snd.to fst

files = filteredM isFile
directories = filteredM isDirectory

contents = act listDirectory

ofSize = undefined
