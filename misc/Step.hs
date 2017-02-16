module Main where

import Control.Monad
import Control.Monad.Free
import Data.Bifunctor

data Step a next = Empty
                 | Symbol a next
                 | Union (Step a next) (Step a next) next
                 | Concat (Step a next) (Step a next) next
                 | Star (Step a next) next
                 deriving Show

instance Functor (Step a) where
    fmap _ Empty = Empty
    fmap f (Symbol x next) = Symbol x (f next)
    fmap f (Union a b next) = Union (fmap f a) (fmap f b) (f next)
    fmap f (Concat a b next) = Concat (fmap f a) (fmap f b) (f next)
    fmap f (Star a next) = Star (fmap f a) (f next)

char :: Char -> Free (Step Char) ()
char c = liftF (Symbol c ())

many :: Free (Step Char) () -> Free (Step Char) ()
many (Free x) = Free (Star x (Pure ()))

test :: Free (Step Char) ()
test = do
    char 'b'
    Free $ (Star (Symbol 'o' (Pure ()))) $ do char 'b'; char 's'

main = undefined
