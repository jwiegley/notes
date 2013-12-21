{-# LANGUAGE TypeOperators #-}

module Profunctor where

import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import Data.Maybe

headMay :: [a] -> Maybe a
headMay [] = Nothing
headMay (a:_) = Just a

maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just a) = [a]

class Profunctor p where
    dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
    dimap f g = lmap f . rmap g

    lmap :: (a -> b) -> p b c -> p a c
    lmap f = dimap f id

    rmap :: (c -> d) -> p b c -> p b d
    rmap = dimap id

instance Profunctor (->) where
    lmap f p = p . f
    rmap f p = f . p

main :: IO ()
main = do
    _ <- runMaybeT . liftIO $ print (10 :: Int)
    _ <- rmap runMaybeT liftIO $ print (10 :: Int)
    print $ headMay [1,2,3]
    print $ fromJust (headMay [1,2,3])
    print $ (rmap fromJust headMay) [1,2,3]
