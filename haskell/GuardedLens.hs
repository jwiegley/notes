module GuardedLens where

import Control.Lens
import Data.Monoid

-- | Turn any lens into a guarded prism.
--
-- >>> (Sum 1,Sum 2) & guarded (\(Sum x) -> x < 100) _1 .~ Sum 150
-- (Sum {getSum = 0},Sum {getSum = 0})
-- >>> (Sum 1,Sum 2) & guarded (\(Sum x) -> x < 100) _1 .~ Sum 50
-- (Sum {getSum = 50},Sum {getSum = 0})
guarded :: Monoid s => (a -> Bool) -> ALens' s a -> Prism' s a
guarded f l = prism'
    (\a -> if f a then storing l a mempty else mempty)
    (\s -> let a = s ^# l
           in if f a
              then Just a
              else Nothing)
