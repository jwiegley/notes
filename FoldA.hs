module FoldA where

import Control.Applicative
import Data.Foldable

foldA :: (Foldable t, Applicative f)
      => (f b -> f a -> f b) -> b -> t a -> f b
foldA f z = go (pure z) . toList
  where
    go r [] = r
    go r (x:xs) = go (f r (pure x)) xs

main :: IO ()
main = do
    xs <- foldA (liftA2 (+)) 0 ([1..10] :: [Int])
    print xs
