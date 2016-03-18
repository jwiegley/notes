{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Reflection where

import Data.Reflection

data Foo a b = Foo a b

instance Functor (Foo a)

instance Applicative (Foo a)

instance (Eq b, Reifies a b, Monoid a) => Monad (Foo a) where
    return = Foo mempty
    s@(Foo x y) >>= f =
        let eq = reflect s :: b -> b -> Bool
            s'@(Foo x' y') = f y in
        if x == x'
        then s'
        else s'
