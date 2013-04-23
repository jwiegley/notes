{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import Control.Monad
import Data.Functor.Identity

data Tree a = Leaf a | Branch (Tree a) (Tree a) deriving (Show, Functor)

data Yoneda f a = Yoneda { runYoneda :: forall b. Functor f => (a -> b) -> f b }

liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda a = Yoneda $ \f -> fmap f a

lowerYoneda :: Functor f => Yoneda f a -> f a
lowerYoneda (Yoneda f) = f id

newtype YonedaEndo a = YonedaEndo { appYonedaEndo :: Yoneda ((->) a) a }

instance Monad YonedaEndo where
    return = YonedaEndo . liftYoneda . const
    YonedaEndo y >>= f = f (lowerYoneda y undefined)

main = do
    -- By using the Yoneda liftYonedading, I can "box up" two different types,
    -- and get a representation for both that has the same result type.
    let y = \f -> runYoneda (liftYoneda (Identity "Hello")) f :: Identity Int
        z = \f -> runYoneda (liftYoneda (Identity 10))      f :: Identity Int

    -- However, even though liftYonedaded values yield the same type, I must
    -- apply functions to them that are appropriate.  For example, I can apply
    -- String -> Int to y, and Int -> Int to z.
    print $ runIdentity $ y length
    print $ runIdentity $ z id

    -- One use of Yoneda is to transform a function into a CPS-version of that
    -- function.  Yoneda's lemma guarantees that this transformed function is
    -- isomorphic to the original.
    let add  x y = x + y
        mult x y = x * y

        cps_liftYoneda = runYoneda . liftYoneda . uncurry

        cpsify_binop f x y cont = cps_liftYoneda f cont (x,y)

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
    -- and ∀b.(a → b) → F b are isomorphic. (Restricting attention to
    -- computable total functions.) This really is a non-trivial statement and
    -- quite surprising when you first see it. Unfortunately it's tricky to
    -- explain without some CS backround.
    --
    -- Nonetheless I'll risk failure and try to explain a specific example
    -- when F is the 'list' functor, assuming a little computing knowledge:
    --
    -- Fix a type a. Suppose you have a (polymorphic) Haskell function f that
    -- for any type b maps functions g:a → b into a list of elements of type
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
        f g xs = runYoneda (liftYoneda xs) g

    print $ notUsingYoneda length ["Hello", "World"]
    print $ f length ["Hello", "World"]

    -- Let's rewrite it a little more point-free:
    let notUsingYoneda' = map
        f' = flip (runYoneda . liftYoneda)

    print $ notUsingYoneda' length ["Hello", "World"]
    print $ f' length ["Hello", "World"]

    -- So, map ≅ flip (runYoneda . liftYoneda)?  What happens if I apply it to
    -- something else... (this f' needs a different type, so we disable the
    -- monomoprhism-restriction up top).
    print $ f' length (Branch (Branch (Leaf "Hello") (Leaf "World!"))
                              (Leaf "And goodbye"))

    -- We see that for any Functor, fmap ≅ flip (runYoneda . liftYoneda)!  But
    -- this is not surprising, because 'liftYoneda' above is defined in terms of
    -- fmap:
    --
    -- f g xs = runYoneda (liftYoneda xs) g
    -- f g xs = runYoneda (Yoneda $ \f -> fmap f xs) g
    -- f g xs = \f -> fmap f xs $ g
    -- f g xs = fmap g xs
    --
    -- So what does the added structure of the Yoneda type buy us?  For one
    -- thing, it is Rank-2 polymorphic in the return type of the function
    -- being fmapped, and hides away the fact of this extra polymorphism.

    -- Edward Kmett writes: "Intuitively, you can view Yoneda as a type level
    -- construction that ensures that you get fmap fusion."  Then he goes on
    -- with another example of its use:
    --
    -- I said one way to define a Monad for Yoneda f was to borrow an
    -- underlying Monad instance for f, but this isn't the only way.
    --
    -- Consider Yoneda Endo: Recall that Endo from Data.Monoid is given by
    -- (see above, before main).  Clearly Endo is not a Monad, it can't even be
    -- a Functor, because a occurs in both positive and negative position.
    --
    -- Nevertheless Yoneda Endo can be made into a monad -- the continuation
    -- passing style version of the Maybe monad!

    let z = YonedaEndo (liftYoneda (+9)) :: YonedaEndo Int
    print $ lowerYoneda (appYonedaEndo (z >>= (\x -> return $ 1 + x))) 20
    print $ lowerYoneda (appYonedaEndo (return 30)) 20

{- Further notes from edwardk:

21:15 <edwardk> Yoneda Endo a = forall r. (a -> r) -> (r -> r)
21:15 <johnw> but I'm getting stuck
21:15 <johnw> yeah, I saw that part
21:15 <monochrom> @type maybe
21:15 <lambdabot> b -> (a -> b) -> Maybe a -> b
21:15 <johnw> but how does "Maybe" behavior come into that at all?
21:15 <edwardk> now, given that what can it do? it can't put the 'r's together.
21:15 <johnw> there's no "empty"
21:15 <edwardk> so it has to either use the function a -> r   -- in which case it has an
          'a' lying around
21:15 <edwardk> or it has to use the 'r'
21:15 <johnw> oh
21:15 <edwardk> in which case it doesn't
21:15 <edwardk> nothing _ r = r
21:15 <edwardk> just a f _ = f a
21:16 <edwardk> add newtype noise and season to taste
21:16 <johnw> ok, let me go chew on that, thanks!
 -}
