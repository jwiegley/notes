module Main where

import Control.DeepSeq
import Numeric.Probability.Distribution
import Control.Monad
import Data.List

f 1 = T' $ fromFreqs [(1, 0.3), (2, 0.7)]
f 2 = T' $ fromFreqs [(1, 0.5), (2, 0.5)]

newtype T' a b = T' { unT' :: T a b }

instance Monad (T' a) where
  return = T' . return
  T' m >>= f = T' $ norm $ m >>= unT' . f

spaceleak = foldl' (>>=) (f 1) $ replicate 25 f :: T' Float Int

main = print $ unT' $ spaceleak
