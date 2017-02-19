module Ran where

import Data.Functor.Kan.Ran
import Data.Maybe

bollu :: Ran Maybe [] a
bollu = toRan go []
  where
    go :: [Maybe a] -> [a]
    go x = x >>= maybeToList
