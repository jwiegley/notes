{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Control.Applicative.Free
       ( Free, effect
       , analyze, eval
       ) where

import Control.Applicative
import Data.Monoid

data Free eff a = Pure a
                | forall b. App (Free eff (b -> a)) (Free eff b)
                | Effect (eff a)

effect = Effect

instance Functor eff => Functor (Free eff) where
    fmap f a = case a of
        Pure x -> Pure (f x)
        App af ax -> App (fmap (f .) af) ax
        Effect eff -> Effect (fmap f eff)

instance Functor eff => Applicative (Free eff) where
    pure = Pure
    (<*>) = App

analyze :: forall f eff a₀ r. (Functor eff, Applicative f, Monoid r)
        => (forall a. eff a -> f r)
        -> Free eff a₀ -> f r
analyze visit = walk
  where
    walk :: forall a. Free eff a -> f r
    walk f = case f of
        Pure _ -> pure mempty
        App af ax -> mappend <$> walk af <*> walk ax
        Effect eff -> visit eff

eval :: forall f eff arr a₀. (Functor eff, Applicative f) => (forall a. eff a -> f a) -> Free eff a₀ -> f a₀
eval exec = go
  where
    go :: forall a. Free eff a -> f a
    go f = case f of
        Pure x -> pure x
        App af ax -> go af <*> go ax
        Effect eff -> exec eff
