{-# LANGUAGE DeriveFunctor #-}

module FreeAdamCS where

import Control.Monad.Free

data LeafF a r = LeafF a r deriving (Functor, Show)

type Rose a = Free (LeafF a) a

rose :: a -> Free (LeafF a) b -> Free (LeafF a) b
rose x xs = Free (LeafF x xs)

leaf :: a -> Free (LeafF a) ()
leaf x = Free (LeafF x (Pure ()))

-- λ> foo
-- Free (LeafF 10 (Free (LeafF 20 (Free (LeafF 30
--         (Free (LeafF 20 (Free (LeafF 30 (Pure 100))))))))))

foo :: Rose Int
foo = do
    rose 10 $ do
        leaf 20
        leaf 30
    leaf 20
    leaf 30
    return 100
