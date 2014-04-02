{-# LANGUAGE UndecidableInstances #-}

module FreeIdentity where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid
import Data.Functor.Identity
import Control.Monad.Free

newtype Fix f = Fix (f (Fix f))

instance Show (f (Fix f)) => Show (Fix f) where
    show (Fix x) = "Fix " ++ show x

toFix :: Free Identity a -> Fix (Either a)
toFix (Pure a) = Fix (Left a)
toFix (Free (Identity a)) = Fix (Right (toFix a))

fromFix :: Fix (Either a) -> Free Identity a
fromFix (Fix (Left a)) = Pure a
fromFix (Fix (Right a)) = Free (Identity (fromFix a))

instance Show (Identity (Free Identity Int)) where
    show (Identity (Pure a)) = "Identity (Pure " ++ show a ++ ")"
    show (Identity (Free a)) = "Identity (Free " ++ show a ++ ")"

main :: IO ()
main = do
    let x = Free (Identity (Free (Identity (Free (Identity (Pure (10 :: Int)))))))
    print x
    print $ toFix x
    print $ fromFix (toFix x)
