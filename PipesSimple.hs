{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

module PipesSimple where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Cont
import Data.Functor.Identity
import Data.Profunctor

-- The current Proxy type

data Proxy a' a b' b m r
    = Request a' (a  -> Proxy a' a b' b m r)
    | Respond b  (b' -> Proxy a' a b' b m r)
    | M (m (Proxy a' a b' b m r))
    | Pure r

-- Boehm-Berarducci encode it

newtype Proxy2 a' a b' b m r = Proxy2 {
    runProxy2 :: forall s.
      (a' -> (a  -> s) -> s) ->
      (b  -> (b' -> s) -> s) ->
      (m s -> s) ->
      (r -> s) ->
      s
}

-- Fold in monadic effects (i.e., don't separate them with M)

newtype Proxy3 a' a b' b m r = Proxy3 {
    runProxy3 :: forall s.
      (a' -> (a  -> m s) -> m s) ->
      (b  -> (b' -> m s) -> m s) ->
      (r -> m s) ->
      m s
}

-- Apply a ContT type wrapper

newtype Proxy4 a' a b' b m r = Proxy4 {
    runProxy4 :: forall s.
      (a' -> ContT s m a) ->
      (b  -> ContT s m b') ->
      ContT s m r
}

-- They are now just arrows in a Kleisli category for 'ContT s m'
--
--   Proxy a' a b' b m r  ≅  (a' ~> a, b ~> b') ~> r

newtype CA s m a b = CA { runCA :: a -> ContT s m b }

instance Profunctor (CA s m) where
    dimap f g (CA k) = CA $ fmap g . k . f

newtype Proxy5 a' a b' b m r = Proxy5 {
    runProxy5 :: forall s. CA s m (CA s m a' a, CA s m b b') r
}

toProxy5 :: Monad m => Proxy a' a b' b m r -> Proxy5 a' a b' b m r
toProxy5 (Request a' fa) = Proxy5 $ CA $ \(req, res) ->
    runCA req a' >>= \a  -> runCA (runProxy5 (toProxy5 (fa  a))) (req, res)
toProxy5 (Respond b fb') = Proxy5 $ CA $ \(req, res) ->
    runCA res b  >>= \b' -> runCA (runProxy5 (toProxy5 (fb' b'))) (req, res)
toProxy5 (M m) = Proxy5 $ CA $ \(req, res) -> ContT $ \k ->
    m      >>= \p  -> runContT (runCA (runProxy5 (toProxy5 p)) (req, res)) k
toProxy5 (Pure r) = Proxy5 $ CA $ \(_req, _res) -> pure r

fromProxy5 :: Monad m => Proxy5 a' a b' b m r -> Proxy a' a b' b m r
fromProxy5 (Proxy5 (CA p)) = M $ flip runContT (return . Pure) $
    p (CA $ \a' -> ContT $ return . Request a' . (M .),
       CA $ \b  -> ContT $ return . Respond b  . (M .))

-- Proxy is also a free monad over a request/respond term algebra
--
-- This was used in older versions of pipes, actually

data Free f a = P a | F (f (Free f a))

data ReqRes a' a b' b r
    = RRequest a' (a  -> r)
    | RRespond b  (b' -> r)

newtype (f :.: g) a = C (f (g a))

type Proxy6 a' a b' b m r = Free (m :.: ReqRes a' a b' b) r

-- -- We can again Boehm-Berarducci encode and apply Cont. What we see is that
-- -- the Free monad teases out the 'm' effects, and drops Cont from the result
-- -- value.

-- newtype ReqRes2 a' a b' b r = ReqRes2 {
--     runReqRes2 :: (a' -> Cont r a) -> (b -> Cont r b') -> r
-- }

-- mapContT' :: (r -> s) -> ContT r m a -> ContT s m a
-- mapContT' f m = ContT $ \(k :: a -> m s) -> liftM f $ runContT m k

-- instance Functor (ReqRes2 a' a b' b) where
--     fmap f (ReqRes2 p) = ReqRes2 $ \g h ->
--         p (mapContT' f . g) h

-- type Proxy7 a' a b' b m r = Free (m :.: ReqRes2 a' a b' b) r

-- toProxy7 :: forall a' a b' b m r. Monad m
--          => Proxy a' a b' b m r -> Proxy7 a' a b' b m r
-- toProxy7 (Request a' fa) = F $ C $ return $ ReqRes2 $ \req res ->
--     flip runCont id $ req a' >>= \a  -> ContT $ \k -> k (toProxy7 (fa  a))
-- toProxy7 (Respond b fb') = F $ C $ return $ ReqRes2 $ \req res ->
--     flip runCont id $ res b  >>= \b' -> ContT $ \k -> k (toProxy7 (fb' b'))
-- toProxy7 (M m) = F $ C $ liftM (\x -> ReqRes2 $ \req res -> toProxy7 x) m
-- toProxy7 (Pure r) = P r

-- fromProxy7 :: Monad m => Proxy7 a' a b' b m r -> Proxy a' a b' b m r
-- fromProxy7 (P p) = Pure p
-- fromProxy7 (F (C p)) = M $ do
--     ReqRes2 g <- liftM (fmap fromProxy7) p
--     let p' = g (\a' -> ContT $ \k -> Identity $ Request a' (runIdentity . k))
--                (\b  -> ContT $ \k -> Identity $ Respond b  (runIdentity . k))
--     return p'

-- -- Now instead of a Kleisli arrow from a pair of Kleisli arrows to a
-- -- result, we have simpler Kleisli arrows (Cont vs. ContT) with structure
-- -- around them:

-- newtype CA2 a b s = CA2 { runCA2 :: a -> Cont s b }

-- newtype (f :*: g) a = R (f a, g a)
-- newtype (f :!: g) a = B (f (g a) a)

-- type Proxy8 a' a b' b m r =
--     Free (m :.: ((->) :!: (CA2 a' a :*: CA2 b' b'))) r

-- toProxy8 :: forall a' a b' b m r. Monad m
--          => Proxy a' a b' b m r -> Proxy8 a' a b' b m r
-- toProxy8 (Request a' fa) = F $ C go
--   where
--     go :: (m :.: ((->) :!: (CA2 a' a :*: CA2 b' b'))) r
--     go = pure $ B $ \(R (req, res)) ->
--         runCA2 req a' >>= \a -> toProxy8 (fa  a)
-- toProxy8 (Respond b fb') = undefined
-- toProxy8 (M m) = undefined
-- toProxy8 (Pure r) = P r
