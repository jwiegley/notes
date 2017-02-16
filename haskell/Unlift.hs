{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unlift where

import Control.Applicative
import Control.Exception
import Control.Concurrent.Async as Async
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Control
import Control.Monad.Trans.Either
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Functor.Identity
import Data.Monoid
import Prelude hiding ((**))

concurrentlyBad :: forall m a b. MonadBaseControl IO m => m a -> m b -> m (a, b)
concurrentlyBad f g =
    liftBaseWith (\run -> Async.concurrently (run f) (run g))
        >>= (\(x, y) -> liftA2 (,) (restoreM x) (restoreM y))

concurrentlyBad_fails = do
    x <- flip runStateT 1 $ liftA (uncurry (+)) (concurrentlyBad go go)
    y <- flip runStateT 1 $ liftA (uncurry (+)) (liftA2 (,) go go)
    print $ x == y
  where
    go = do
        y <- get
        let z = y + 10
        put z
        return z

-- | Monoids which are also commutative
--
-- This type class introduces no new operations, but rather a single law:
-- @
-- mappend x y = mappend y x
-- @
class Monoid m => Commutes m

instance Commutes ()
instance Commutes m => Commutes (Maybe m)
instance Num a => Commutes (Sum a)
instance Num a => Commutes (Product a)
instance Commutes Ordering
instance Commutes Any
instance Commutes All
instance Commutes b => Commutes (a -> b)
instance (Commutes a, Commutes b, Commutes c, Commutes d)
         => Commutes (a, b, c, d)
instance (Commutes a, Commutes b, Commutes c) => Commutes (a, b, c)
instance (Commutes a, Commutes b) => Commutes (a, b)
instance Commutes a => Commutes (Const a b)

-- | Applicative functors which are also commutative
--
-- This type class introduces no new operations, but rather a single law:
-- @
-- liftA2 ($) x y = liftA2 (flip ($)) y x
-- @
class Applicative f => Commutative f

instance Commutative IO
instance Commutative (ST s)
instance Commutative STM
instance Commutative Identity
instance Commutative Maybe                   -- false if we consider bottoms
instance Commutes w => Commutative (Either w) -- false if we consider bottoms
instance Commutative ((->) r)
instance Commutative m => Commutative (IdentityT m)
instance Commutative m => Commutative (ReaderT r m)
instance (Monad m, Commutative m) => Commutative (MaybeT m)
instance (Commutative m, Commutes w) => Commutative (WriterT w m)
instance (Monad m, Commutative m, Commutes w) => Commutative (EitherT w m)
instance Commutes w => Commutative (Const w)

concurrently :: (MonadBaseControl IO m, Commutative m) => m a -> m b -> m (a, b)
concurrently f g =
    liftBaseWith (\run -> Async.concurrently (run f) (run g))
        >>= (\(x, y) -> liftA2 (,) (restoreM x) (restoreM y))

combineM x y = liftBaseWith (\run -> liftA2 (,) (run x) (run y))
                   >>= (\(a, b) -> liftA2 (,) (restoreM a) (restoreM b))

concurrently_passes = do
    x <- flip runReaderT 1 $ liftA (uncurry (+)) (Unlift.concurrently go go)
    y <- flip runReaderT 1 $ liftA (uncurry (+)) (liftA2 (,) go go)
    print $ x == y
  where
    go = do
        y <- ask
        let z = y + 10
        return z

{-
-- A followup to our discussion above: The type of 'concurrently' is exactly
-- that of '**', from the Monoidal definition of Applicative functors
-- presented here:
--
--     http://blog.ezyang.com/2012/08/applicative-functors/

class Functor f => Monoidal f where
  unit :: f ()
  (**) :: f a -> f b -> f (a,b)

-- Now, StateT IO is trivially Monoidal, because we can define '**' in terms
-- of chaining computations:

instance Monoidal IO where
    unit = pure ()
    (**) = liftA2 (,)

instance (Functor m, Monad m) => Monoidal (StateT s m) where
    unit = StateT $ \s -> return ((), s)
    StateT f ** StateT g = StateT $ \s -> do
        (a, s')  <- f s
        (b, s'') <- g s'
        return ((a, b), s'')

-- But implementing this same function using monad-control creates a problem,
-- for although it type checks, the use of MonadBaseControl requires that we
-- entirely separate the computations, and then recombine both their results
-- *and* their contexts after.

newtype Bad s m a = Bad (StateT s m a) deriving (Functor, Applicative, Monad)

combine :: forall m a b. MonadBaseControl IO m => m a -> m b -> m (a, b)
combine f g = control $ \run ->
    go run =<< run f ** run g
  where
    go :: (forall x. m x -> IO (StM m x))
       -> (StM m a, StM m b)
       -> IO (StM m (a, b))
    go run (x, y) = run $ liftM2 (,) (restoreM x :: m a) (restoreM y :: m b)

instance (Functor m, MonadBaseControl IO m) => Monoidal (Bad s m) where
    unit = Bad $ StateT $ \s -> return ((), s)
    Bad f ** Bad g = Bad $ combine f g

-- This is applicable to a subset of applicative functors, however:
-- commutative applicative functors, discussed somewhat here:
--
--     http://tomasp.net/blog/applicative-functors.aspx/.
--
-- Such a commutative functor offers us a monoid homomorphism (in the category
-- of endofunctors), such that the following functions exist:

k :: MonadBaseControl b m => (m x -> m y -> m (x, y)) -> b x -> b y -> b (x, y)
k f x y = undefined

g :: MonadBaseControl b m => (b x -> b y -> b (x, y)) -> m x -> m y -> m (x, y)
g f x y = undefined

-- With the requirement that: k . g = g . k = id

-- What we lack is a natural isomorphism between the StateT IO and IO
-- Applicative functors, or functions:
--
-- forall x. StateT
-}

main = concurrentlyBad_fails
