> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE UndecidableInstances #-}
>
> module FreeMaybe where
>
> import Control.Monad (join)
> import Control.Monad.Writer.Class

There can be just two values of type Maybe a: Nothing and Just a.  Let's look
at the Free monad of Maybe a, Free Maybe a:

> data Free f a = Pure a | Free (f (Free f a))
>
> instance Functor f => Functor (Free f) where
>     fmap f (Pure a)   = Pure (f a)
>     fmap f (Free ffa) = Free $ fmap (fmap f) ffa
>
> instance Functor f => Monad (Free f) where
>     return = Pure
>     Pure a >>= f = f a
>     Free ffa >>= f = Free $ fmap (>>= f) ffa
>
> instance (Show a, Show (f (Free f a))) => Show (Free f a) where
>     showsPrec d (Pure a) = showParen (d > 10) $
>         showString "Pure " . showsPrec 11 a
>     showsPrec d (Free m) = showParen (d > 10) $
>         showString "Free " . showsPrec 11 m

There are four "shapes" that values of type Free Maybe a can take:

    Pure a
    Free Nothing
    Free (Just (Free (Just (... (Free Nothing)))))
    Free (Just (Free (Just (... (Free (Pure a))))))

In terms of whether a `Free Maybe a` represents an `a` or not, `Free Maybe a`
is equivalent to `Maybe a`.  However, `Maybe a` is *right adjoint* to `Free
Maybe a`, meaning that it forgets some of the structure of `Maybe a` --
namely, which of the four shapes above the value was, and how many occurences
of `Free (Just` there were.

Why would you ever use `Free Maybe a`?  *Precisely if you cared about the
number of Justs*.  Now, say we had a functor that carried other information:

> data Info a = Info { infoExtra :: String, infoData :: a }
>     deriving (Show, Functor)

Then `Free Info a` is isomorphic to if `infoExtra` had been `[String]`:

> main :: IO ()
> main = do
>     print $ Free (Info "Hello" (Free (Info "World" (Pure "!"))))

> foo :: IO ()
> foo = do
>     print $ do
>         x <- Free (Info "Hello" (Pure "!"))
>         y <- Free (Info "World" (Pure "!"))
>         return $ x ++ y
