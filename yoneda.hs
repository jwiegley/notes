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
    -- get a representation for both that has the same type.  I can now pass
    -- this around to code which only accepts the one type, Identity Int.
    let y = \f -> runYoneda (embed (Identity "Hello")) f :: Identity Int
        z = \f -> runYoneda (embed (Identity 10))      f :: Identity Int

    -- However, even though embedded values have the same type, I can only
    -- apply functions to them which are appropriate to the underlying type.
    -- In this case, I apply String -> Int to y, and Int -> Int to z.
    print $ runIdentity $ y length
    print $ runIdentity $ z id

    -- If I try to treat all of the embedded values as the same type, I'll get
    -- a type error.  Just uncomment this line and try to compile it!
    -- print $ map (runIdentity . ($ length)) [y,z]
