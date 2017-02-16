{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}

module FreeAdamCS where

import Control.Monad.Free

data RoseF a r
    = Branch a r
    | Split r r
    deriving (Functor, Show)

type Rose a = Free (RoseF a)

rose :: a -> Rose a b -> Rose a b
rose x xs = Free (Branch x (Free (Split xs xs)))

leaf :: a -> Rose a ()
leaf x = Free (Branch x (Pure ()))

foo :: Rose Int Int
foo = rose 1 $ do
    x <- rose 10 $ do
        leaf 20
        leaf 30
        return 50
    leaf (20 + x)
    leaf 30
    return 100
