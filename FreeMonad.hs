module FreeMonad where

import Control.Monad.Free
import Data.Monoid

nfoldr :: Functor f
       => (forall x. f (f x) -> f x) -> (a -> f a) -> Free f a -> f a
nfoldr _ r (Pure a) = r a
nfoldr j r (Free m) = j $ fmap (nfoldr j r) m

main = print $ nfoldr (\(y, (z, a)) -> (y <> z, a)) (\y -> (mempty, y)) x
  where
    b = Pure ("Hi" :: String)
    x = Free (Sum (1 :: Int),
              Free (Sum 2, Free (Sum 3, Free (Sum 4, Free (Sum 5, b)))))
