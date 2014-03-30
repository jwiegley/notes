This article assumes familiarity with monads and monad transformers.  If
you've never had an occasion to use `lift` yet, you may want to come back to
it later.

## The Problem

What is the problem that `monad-control` aims to solve?  To answer that, let's
back up a bit.  We know that a monad represents some kind of "computational
context".  The question is, can we separate this context from the monad, and
reconstitute it later?  If we know the monadic types involved, then for some
monads we can.  Consider the `State` monad: it's essentially a function from
an existing state, to a pair of some new state and a value.  It's fairly easy
then to extract its state and later use it to "resume" that monad:

``` active haskell
import Control.Applicative
import Control.Monad.Trans.State

main = do
    let f = do { modify (+1); show <$> get } :: StateT Int IO String
    
    (x,y) <- runStateT f 0
    print $ "x = " ++ show x   -- x = "1"
    
    (x2,y2) <- runStateT f y
    print $ "x = " ++ show x2  -- x = "2"
```

In this way, we interleave between `StateT Int IO` and `IO`, by completing the
`StateT` invocation, obtaining its state as a value, and starting a new
`StateT` block from the prior state.  We've effectively resumed the earlier
`StateT` block.

## Nesting calls to the base monad

But what if we didn't, or couldn't, exit the `StateT` block to run our `IO`
computation?  In that case we'd need to use `liftIO` to enter `IO` and make a
nested call to `runStateT` inside that `IO` block.  Further, we'd want to
restore any changes made to the inner `StateT` within the outer `StateT`,
after returning from the `IO` action:

``` active haskell
import Control.Applicative
import Control.Monad.Trans.State
import Control.Monad.IO.Class

main = do
    let f = do { modify (+1); show <$> get } :: StateT Int IO String

    flip runStateT 0 $ do
        x <- f
        y <- get
        y' <- liftIO $ do
            print $ "x = " ++ show x   -- x = "1"

            (x',y') <- runStateT f y
            print $ "x = " ++ show x'  -- x = "2"
            return y'
        put y'
```

## A generic solution

This works fine for `StateT`, but how can we write it so that it works for any
monad tranformer over IO?  We'd need a function that might look like this:

``` haskell
foo :: MonadIO m => m String -> m String
foo f = do
    x <- f
    y <- getTheState
    y' <- liftIO $ do
        print $ "x = " ++ show x

        (x',y') <- runTheMonad f y
        print $ "x = " ++ show x'
        return y'
    putTheState y'
```

But this is impossible, since we only know that `m` is a `Monad`.  Even with a
`MonadState` constraint, we would not know about a function like
`runTheMonad`.  This indicates we need a type class with at least three
capabilities: getting the current monad tranformer's state, executing a new
transformer within the base monad, and restoring the enclosing transformer's
state upon returning from the base monad.  This is exactly what
`MonadBaseControl` provides, from `monad-control`:

``` haskell
class MonadBase b m => MonadBaseControl b m | m -> b where
    data StM m :: * -> *
    liftBaseWith :: (RunInBase m b -> b a) -> m a
    restoreM :: StM m a -> m a
```

Taking this definition apart piece by piece:

1. The `MonadBase` constraint exists so that `MonadBaseControl` can be used
   over multiple base monads: `IO`, `ST`, `STM`, etc.

2. `liftBaseWith` combines three things from our last example into one: it
   gets the current state from the monad transformer, wraps it an `StM` type,
   lifts the given action into the base monad, and provides that action with a
   function which can be used to resume the enclosing monad within the base
   monad.  When such a function exits, it returns a new `StM` value.
   
3. `restoreM` takes the encapsulated tranformer state as an `StM` value, and
   applies it to the parent monad transformer so that any changes which may
   have occurred within the "inner" transformer are propagated out.  (This
   also has the effect that later, repeated calls to `restoreM` can "reset"
   the transformer state back to what it was previously.)

## Using monad-control and liftBaseWith

With that said, here's the same example from above, but now generic for any
transformer supporting `MonadBaseControl IO`:

``` active haskell
{-# LANGUAGE FlexibleContexts #-}

import Control.Applicative
import Control.Monad.Trans.State
import Control.Monad.Trans.Control

foo :: MonadBaseControl IO m => m String -> m String
foo f = do
    x <- f
    y' <- liftBaseWith $ \runInIO -> do
        print $ "x = " ++ show x   -- x = "1"

        x' <- runInIO f
        -- print $ "x = " ++ show x'

        return x'
    restoreM y'

main = do
    let f = do { modify (+1); show <$> get } :: StateT Int IO String

    (x',y') <- flip runStateT 0 $ foo f
    print $ "x = " ++ show x'   -- x = "2"
```

One notable difference in this example is that the second `print` statement in
`foo` becomes impossible, since the "monadic value" returned from the inner
call to `f` must be restored and executed within the outer monad.  That is,
`runInIO f` is executed in IO, but it's result is an `StM m String` rather
than `IO String`, since the computation carries monadic context from the inner
transformer.  Converting this to a plain `IO` computation would require
calling a function like `runStateT`, which we cannot do without knowing which
transformer is being used.

As a convenience, since calling `restoreM` after exiting `liftBaseWith` is so
common, you can use `control` instead of `restoreM =<< liftBaseWith`:

``` haskell
    y' <- restoreM =<< liftBaseWith (\runInIO -> runInIO f)

    -- becomes...
    y' <- control $ \runInIO -> runInIO f
```

Another common pattern is when you don't need to restore the inner
transformer's state to the outer transformer, you just want to pass it down as
an argument to some function in the base monad:

``` haskell
foo :: MonadBaseControl IO m => m String -> m String
foo f = do
    x <- f
    liftBaseDiscard forkIO $ f
```

In this example, the first call to `f` affects the state of `m`, while the
inner call to `f`, though inheriting the state of `m` in the new thread, but
does not restore its effects to the parent monad transformer when it returns.

Now that we have this machinery, we can use it to make any function in `IO`
directly usable from any supporting transformer.  Take `catch` for example:

``` haskell
catch :: Exception e => IO a -> (e -> IO a) -> IO a
```

What we'd like is a function that works for any `MonadBaseControl IO m`,
rather than just `IO`.  With the `control` function this is easy:

``` haskell
catch :: (MonadBaseControl IO m, Exception e) => m a -> (e -> m a) -> m a
catch f h = control $ \runInIO -> catch (runInIO f) (runInIO . h)
```

You can find many function which are generalized like this in the packages
`lifted-base` and `lifted-async`.
