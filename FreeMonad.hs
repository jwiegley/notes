module Main where

import Control.Monad.Free

hackrilege_to :: Functor m => Free m (Free m a) -> Free m a
hackrilege_to (Pure (Pure x)) = Pure x
hackrilege_to (Pure (Free x)) = Free x
hackrilege_to (Free x) = Free (fmap hackrilege_to x)

hackrilege_from :: Functor m => Free m a -> Free m (Free m a)
hackrilege_from (Pure x) = Pure (Pure x)
hackrilege_from (Free x) = Free (fmap hackrilege_from x)

main = undefined
