{-# LANGUAGE RankNTypes #-}

module Combining where

import Control.Lens

selecting :: Lens' s a -> Lens' s a' -> Lens' s (a, a')
selecting x x' =
    lens (\s -> (s ^. x, s ^. x'))
         (\s (b, b') -> s & set x b & set x' b')

main :: IO ()
main = do
    print $ (1,2,3,4) ^. selecting _2 _4
    print $ (1,2,3,4)  & selecting _2 _4 .~ (10, 20)
