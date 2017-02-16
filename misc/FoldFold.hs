module FoldFold where

import Data.Foldable

foldfold :: Foldable t
         => (a -> b -> b) -> (a -> c -> c) -> b -> c -> t a -> (b, c)
foldfold f g z w = go z w . toList
  where
    go b c []     = (b, c)
    go b c (x:xs) = go (f x b) (g x c) xs

{-# RULES "fold/fold"
      forall (f :: forall a b. (a -> b -> b))
             (g :: forall a b. (a -> b -> b)) (z :: forall a. a) w xs.
        (foldr f z xs, foldr g w xs) = foldfold f g z w xs #-}

main :: IO ()
main = print (foldr (+) 0 [1, 2, 3, 4, 5], foldr (*) 0 [1, 2, 3, 4, 5])
