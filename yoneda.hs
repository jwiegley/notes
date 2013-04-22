{-# LANGUAGE RankNTypes #-}

module Main where

import Data.Functor.Identity

data Yoneda f a = Yoneda
    { runYoneda :: forall b. Functor f => (a -> b) -> f b
    }

embed :: Functor f => f a -> Yoneda f a
embed a = Yoneda $ \f -> fmap f a

unembed :: Functor f => Yoneda f a -> f a
unembed y = runYoneda y id

main = do
    -- By using the Yoneda embedding, I can "box up" two different types, and
    -- get a representation for both that has the same result type.
    let y = \f -> runYoneda (embed (Identity "Hello")) f :: Identity Int
        z = \f -> runYoneda (embed (Identity 10))      f :: Identity Int

    -- However, even though embedded values yield the same type, I must apply
    -- functions to them that are appropriate.  For example, I can apply
    -- String -> Int to y, and Int -> Int to z.
    print $ runIdentity $ y length
    print $ runIdentity $ z id

    -- If I try to treat all of the embedded values as if they had embedded
    -- the same type, I'll get a type error.  Just uncomment this line below
    -- and try to compile it!
    -- print [y,z]
