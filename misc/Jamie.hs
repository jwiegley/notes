{-# LANGUAGE OverloadedStrings #-}

module Jamie where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.State
import Data.Maybe
import Data.List
import Data.Monoid

-- takes a String input; if parsing succeeds, it returns parsed value along with remaining input
newtype Parser a
  = Parser { runParser :: String -> Maybe (a, String) }

first :: (a -> b) -> (a,c) -> (b,c)
first f (a,c) = (f a, c)

instance Functor Parser where
  fmap f (Parser p) = Parser $ fmap (first f) . p

{-- Implement an Applicative instance for Parser:
   `pure a'    represents the parser which consumes no input and successfully returns a result of a.
   `p1 <*> p2' represents the parser which first runs p1 (which will consume some input and produce a
               function), then passes the remaining input to p2 (which consumes more input and produces
               some value), then returns the result of applying the function to the value. However, if
               either p1 or p2 fails then the whole thing should also fail (put another way, p1 <*> p2
               only succeeds if both p1 and p2 succeed).
--}

instance Applicative Parser where
  pure a    = Parser (\s -> Just (a,s))
  Parser p1 <*> Parser p2 = Parser $ runStateT (StateT p1 <*> StateT p2)

main :: IO ()
main = undefined
