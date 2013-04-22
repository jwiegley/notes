{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import Data.Functor.Identity

data Yoneda f a = Yoneda
    { runYoneda :: forall b. Functor f => (a -> b) -> f b
    }

embed :: Functor f => f a -> Yoneda f a
embed a = Yoneda $ \f -> fmap f a

unembed :: Functor f => Yoneda f a -> f a
unembed y = runYoneda y id

data Tree a = Leaf a | Branch (Tree a) (Tree a) deriving (Show, Functor)

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

    -- Dan Piponi writes of Yoneda:
    --
    -- If you program in a pure functional programming language like Haskell
    -- then the Yoneda lemma tells you that for any functor F, the types Fa
    -- and ∀b.(a→b)→Fb are isomorphic. (Restricting attention to computable
    -- total functions.) This really is a non-trivial statement and quite
    -- surprising when you first see it. Unfortunately it's tricky to explain
    -- without some CS backround.
    --
    -- Nonetheless I'll risk failure and try to explain a specific example
    -- when F is the 'list' functor, assuming a little computing knowledge:
    --
    -- Fix a type a. Suppose you have a (polymorphic) Haskell function f that
    -- for any type b maps functions g:a→b into a list of elements of type
    -- b. Then f is equal to a function that applies g elementwise to some
    -- fixed list of elements of a. It's a powerful result. Just knowing the
    -- type of the function f is enough to deduce significant detail about
    -- what it does. It can reduce the amount of work required to prove the
    -- correctness of programs.
    --
    -- The crucial thing that makes this work is that Haskell uses "parametric
    -- polymorphism". If you write a function that is polymorphic it's
    -- impossible to use specific knowledge about the type, you have to write
    -- your function generically to work with all possible types.

    -- Here is an example of what he's describing:
    let notUsingYoneda g xs = map g xs
        f g xs = runYoneda (embed xs) g

    print $ notUsingYoneda length ["Hello", "World"]
    print $ f length ["Hello", "World"]

    -- Let's rewrite it a little more point-free:
    let notUsingYoneda' = map
        f' = flip (runYoneda . embed)

    print $ notUsingYoneda' length ["Hello", "World"]
    print $ f' length ["Hello", "World"]

    -- So, map ≅ flip (runYoneda . embed)?  What happens if I apply it to
    -- something else... (this f' needs a different type, so we disable the
    -- monomoprhism-restriction up top).
    print $ f' length (Branch (Branch (Leaf "Hello") (Leaf "World!"))
                              (Leaf "And goodbye"))

    -- We see that for any Functor, fmap ≅ flip (runYoneda . embed)!  But this
    -- is not surprising, because 'embed' above is defined in terms of fmap:
    --
    -- f g xs = runYoneda (embed xs) g
    -- f g xs = runYoneda (Yoneda $ \f -> fmap f xs) g
    -- f g xs = \f -> fmap f xs $ g
    -- f g xs = fmap g xs
    --
    -- So what does the added structure of the Yoneda type buy us?  *It is
    -- Rank-2 polymorphic in the return type of the function being fmapped*,
    -- and hides this polymorphism quite nicely.
