--{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module ContThoughts where

import Control.Applicative
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Functor.Compose

{-

Implementing ContT without looking at the definitions in transformers...

-}

newtype ContT r m a = ContT { runContT :: (a -> m r) -> m r }

instance Functor (ContT r m) where
    fmap f (ContT k) = ContT $ \h -> k (h . f)

instance Applicative (ContT r m) where
    pure x = ContT $ \k -> k x
    ContT f <*> ContT k = ContT $ \h -> f (\g -> k (h . g))

instance Monad (ContT r m) where
    return = pure
    ContT m >>= f = ContT $ \k -> m (\a -> runContT (f a) k)

{-

Cont and ContT are incredibly close.  Just drop 'm' from the type, and change
all occurences of ContT to Cont, and that's it!  The instances are identical;
it's only the types that differ.

-}

newtype Cont r a = Cont { runCont :: (a -> r) -> r }

instance Functor (Cont r) where
    fmap f (Cont k) = Cont $ \h -> k (h . f)

instance Applicative (Cont r) where
    pure x = Cont $ \k -> k x
    Cont f <*> Cont k = Cont $ \h -> f (\g -> k (h . g))

instance Monad (Cont r) where
    return = pure
    Cont m >>= f = Cont $ \k -> m (\a -> runCont (f a) k)

{-

Consider an ordinary chain of function application:

    h (g (f x))

In the "pure identity" monad (where "m a ~ a"), this is equivalent to:

    ((return x >>= f) >>= g) >>= h

Which is equivalent to the Cont form:

    ((return x >>= f) >>= g) >>= h $ id

Proof:

      ((return x >>= f) >>= g) >>= h $ id

      <definition of return for Cont>
    = (((\k -> k x) >>= f) >>= g) >>= h $ id

      <definition of >>= for Cont>
    = ((\z -> (\k -> k x) (\a -> f a z)) >>= g) >>= h $ id

      <function application>
    = ((\z -> (\a -> f a z) x) >>= g) >>= h $ id

      <function application>
    = ((\z -> f x z) >>= g) >>= h $ id

      <definition of >>= for Cont>
    = (\y -> (\z -> f x z) (\a -> g a y)) >>= h $ id

      <function application>
    = (\y -> f x (\a -> g a y)) >>= h $ id

      <function application>
    = (\w -> (\y -> f x (\a -> g a y)) (\a -> h a w)) $ id

      <definition of >>= for Cont>
    = (\w -> f x (\a -> g a (\a -> h a w))) $ id

      <function application>
    = f x (\a -> g a (\a -> h a id))

      <function application>
    = g (f x) (\a -> h a id)

      <function application>
    = h (g (f x)) $ id

The most expanded form, \w -> f x (\a -> g a (\a -> h a w)), is a lambda
abstraction where each step of the evaluation receives a lambda representing
the remainder of the work to be done.  This allows us to write a function
`callCC` to make these inner lambdas available (sadly, I was unable to
implement this without ultimately looking at the definition from
'transformers'; in the future I will have to try again from scratch):

-}

callCC :: ((a -> ContT r m b) -> ContT r m a) -> ContT r m a
callCC f = ContT $ \h -> runContT (f $ \a -> ContT $ \_ -> h a) h

--         f      hg
-- label :: ContT ((ContT r m a -> m r) -> m r)
label :: ContT r m (ContT r m a)
label = callCC $ \k -> let m = k m in return m

-- 'label' with the callCC expanded:
label' :: ContT r m (ContT r m a)
label' = ContT $ \h -> runContT (let m = ContT $ \_ -> h m in return m) h

-- (ContT r m a -> m r) -> (ContT r m a -> m r) -> m r

{-

In English: callCC returns a ContT which receives the next function in the
sequence to call, 'h' (the next statement in the ContT block, after the callCC
block).  It then runs the sub-continuation provided to callCC; this
sub-continuation itself receives a function which, if called with an 'a',
returns a continuation that ignores the next function in the sequence (i.e.,
the remainer of the sub-continuation), and just invokes 'h'.  Or, if the
function passed to the sub-continuation is never called, it does the same, in
both cases resuming to 'h'.

Here it is, translated into our "pure identity monad" (m a ~ a):

    callCC f = \h -> f (const . h) h

It's clearer in this form that callCC takes a lambda which calls 'h' in two
cases: as the result of the body of f calling (const . h) and thereby the 'h'
continuation, or as the result of 'h' being called as the continuation from f.
All roads lead to 'h'.

The pointfree definition in this monad is deceptively simple, given how
complex callCC can seem to be:

    callCC = ((const .) >>=)

-}

{-

Here is yet another expression of Cont, as the composition of two
hom-functors:

-}

newtype Hom r a = Hom { getHom :: a -> r }

type Cont' r a = Compose (Hom r) (Hom r) a

instance Monad (Compose (Hom r) (Hom r)) where
    return x = Compose $ Hom $ \h -> getHom h x
    Compose (Hom m) >>= f =
        Compose $ Hom $ \k -> m (Hom $ \a -> getHom (getCompose (f a)) k)

{-

Since the Cont Monad is just H . H, with H being a hom-functor, we can see
that it arises from self-adjunction.

-}

instance MonadIO m => MonadIO (ContT r m) where
    liftIO = lift . liftIO

instance (Monad m, MonadIO m, Applicative m) => MonadBase IO (ContT r m) where
    liftBase = liftIO

instance MonadTrans (ContT r) where
    lift m = ContT (m >>=)

-- instance MonadTransControl (ContT r) where
--     newtype StT (ContT r) a = StContT { unContT :: StT (ContT r) a }
--     liftWith = defaultLiftWith id id StContT
--     restoreT = defaultRestoreT StContT unContT

-- instance (MonadIO m, MonadBaseControl IO m)
--          => MonadBaseControl IO (ContT r m) where
--     newtype StM (ContT r m) a = StMT { unStMT :: ComposeSt (ContT r) m a }
--     liftBaseWith = defaultLiftBaseWith StMT
--     restoreM     = defaultRestoreM unStMT

void m = m >> return ()

main :: IO ()
main = void $ flip runContT return $ do
    liftIO $ putStrLn "step 1.."
    v <- callCC $ \k -> do
        liftIO $ putStrLn "step 2.."
        -- liftIO $ do
        --     liftIO $ putStrLn "step 3.."
        --     runContT (k "after step 3") return
        --     liftIO $ putStrLn "step 4.."

        -- m <- control $ \runInIO -> do
        --     liftIO $ putStrLn "step 5.."
        --     m <- runInIO $ do
b        --          return "step 6.."
        --          k "after step 5"
        --          return "step 7.."
        --     liftIO $ putStrLn "step 8.."
        --     return m
        -- return $ "after step 9: " ++ m
        return "foo"

    liftIO $ putStrLn $ "step 10: " ++ v
    return "Hello"
