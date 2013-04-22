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

    -- One use of Yoneda is to transform a function into a CPS-version of that
    -- function.  Yoneda's lemma guarantees that this transformed function is
    -- isomorphic to the original.
    let add  x y = x + y
        mult x y = x * y

        cps_embed = runYoneda . embed . uncurry

        cpsify_binop f x y cont = cps_embed f cont (x,y)

        cps_add  = cpsify_binop add
        cps_mult = cpsify_binop mult

    putStrLn "Result of normal math:"
    print $ add (mult (add 4 5) 2) 2

    putStrLn "Result of CPS math:"
    print $ cps_add 4 5 (\x -> cps_mult x 2 (\x -> cps_add x 2 id))
