module Nikita where

import Control.Applicative
import Control.Monad
import Data.Semigroup

-- A version of ListT that I do not care for.

newtype ListT m a = ListT { runListT :: Maybe (a, m (ListT m a)) }

instance Applicative m => Semigroup (ListT m a) where
    ListT Nothing <> y = y
    x <> ListT Nothing = x
    ListT (Just (a, x)) <> y =
        ListT (Just (a, liftA2 (<>) x (pure y)))

instance Functor m => Functor (ListT m) where
    fmap _ (ListT Nothing) = ListT Nothing
    fmap f (ListT (Just (a, m))) = ListT (Just (f a, fmap (fmap f) m))

instance Applicative m => Applicative (ListT m) where
    pure x = ListT $ Just (x, pure (ListT Nothing))
    (<*>) = undefined

instance Monad m => Monad (ListT m) where
    return x = ListT $ Just (x, return (ListT Nothing))
    ListT Nothing >>= _ = ListT Nothing
    ListT (Just (a, m)) >>= f = ListT $ case f a of
        ListT Nothing -> Nothing
        ListT (Just (b, m')) -> Just (b, liftM2 (<>) (liftM (>>= f) m) m')
