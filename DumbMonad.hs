module DumbMonad where

import           Control.Applicative
import           Control.Monad
import           Data.Set (Set)
import qualified Data.Set as S

instance Functor Set where
  fmap f x = S.mapMonotonic f x

instance Applicative Set where
  f <*> x = fmap (head (S.toList f)) x

instance Monad Set where
  return x = S.singleton x
  x >>= f  = S.foldr S.union S.empty (S.mapMonotonic f x)

foo :: Set Int -> Set Int
foo x = do
  y <- (+1) <$> x
  return y

main :: IO ()
main = print $ foo (S.fromList [1, 2, 3])