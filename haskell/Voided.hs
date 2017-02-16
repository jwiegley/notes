module Voided where

import Control.Applicative
import Control.Lens
import Data.Void

newtype Voided a = Voided Void

instance Functor Voided where
    fmap _ (Voided v) = absurd v

foo = case undefined of
        Left _ -> _Left
        Right _ -> undefined

instance Applicative Voided where
    pure _ = absurd undefined
    Voided _ <*> Voided x = absurd x

instance Monad Voided where
    return = pure
    Voided m >>= _ = absurd m
