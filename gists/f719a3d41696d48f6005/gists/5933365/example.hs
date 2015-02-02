module Main where

import Control.Monad
import Control.Monad.Trans.State

foo :: [a] -> [(Int,a)]
foo xs = flip evalState 0 $ do
    foldM (\acc x -> do
                idx <- get
                modify (+1)
                return $ acc ++ [(idx,x)]) [] xs

main = print $ foo ['a','b','c','d','e']
