{-# LANGUAGE RankNTypes #-}

module Lenses where

import Control.Applicative
import Control.Lens
import Control.Lens.Reified
import Control.Monad
import Data.Functor.Identity
import Data.Profunctor

k :: Lens' (a, b) a -> (a -> Maybe a) -> (a, b) -> Maybe (a, b)
k x f = x $ f

newtype FlipLens a b s t = FlipLens { unflipLens :: Lens s t a b }

instance Profunctor (FlipLens a b) where
    dimap f g (FlipLens h) = FlipLens $ \k s -> fmap g (h k (f s))

instance Functor (FlipLens a b s) where
    fmap = rmap

newtype FlipTraversal a b s t =
    FlipTraversal { unflipTraversal :: Traversal s t a b }

instance Profunctor (FlipTraversal a b) where
    dimap f g (FlipTraversal h) = FlipTraversal $ \k s -> fmap g (h k (f s))

instance Functor (FlipTraversal a b s) where
    fmap = rmap

instance Applicative (FlipTraversal a b s) where
    pure x = FlipTraversal $ \_ _ -> pure x
    FlipTraversal f <*> FlipTraversal x =
        FlipTraversal $ \k s -> f k s <*> x k s

main = do
    print $ (1,3) ^. runLens (Lens _1)
    print $ ("1","3") &
        unflipLens (lmap (fmap (read :: String -> Int))
                  $ rmap (fmap show) $ FlipLens _2) .~ 4
    print $ [(((+1),3) :: (Int->Int,Int))] ^..
        traverse.unflipTraversal (FlipTraversal _2)
