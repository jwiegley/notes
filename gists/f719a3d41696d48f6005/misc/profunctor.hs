{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

module Profunctor where

import Control.Lens.Internal.Indexed
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import Data.Copointed
import Data.Maybe
import GHC.Exts

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

class (Functor f, Profunctor p) => PApplicative f p where
    pure :: a -> p (f ()) (f a)
    (<*>) :: f (p a b) -> p (f a) (f b)

instance (Functor f, Copointed f) => PApplicative f (->) where
    pure x = fmap (\() -> x)
    (<*>) = copoint . fmap distrib

main :: IO ()
main = do
    _ <- runMaybeT . liftIO $ print (10 :: Int)
    _ <- rmap runMaybeT liftIO $ print (10 :: Int)
    print $ headMay [1,2,3]
    print $ fromJust (headMay [1,2,3])
    print $ (rmap fromJust headMay) [1,2,3]
