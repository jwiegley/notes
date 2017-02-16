{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}

module TwanFree where

import Control.Monad.Free

class Num a => F a

data TermF r = PutChar Char r
             | GetChar (Char -> r)
             deriving Functor

data Term m = Term {
    putChar :: Char -> m (),
    getChar :: m Char
}

data TFree effect a = TFree { runTFree :: forall m. Monad m => effect m -> m a }

to :: Free TermF a -> TFree Term a
to (Pure x) = TFree $ \_ -> return x
to (Free (PutChar x next)) = TFree $ \e -> do
    TwanFree.putChar e x
    runTFree (to next) e
to (Free (GetChar f)) = TFree $ \e -> do
    x <- TwanFree.getChar e
    runTFree (to (f x)) e

from :: TFree Term a -> Free TermF a
from (TFree f) = f Term
  { TwanFree.putChar = \x -> Free (PutChar x (Pure ()))
  , TwanFree.getChar = Free (GetChar Pure)
  }
