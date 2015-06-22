{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module PipesSimple where

import Control.Applicative
import Control.Monad.Trans.Cont
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


-- Proxy is also a free monad over a request/respond term algebra that allows
-- monadic effects
--
-- This was used in older versions of pipes, actually

data Free f a = P a | F (f (Free f a))

data ReqRes a' a b' b r
    = RRequest a' (a  -> r)
    | RRespond b  (b' -> r)

newtype (f :.: g) a = C (f (g a))

type Proxy6 a' a b' b m r = Free (m :.: ReqRes a' a b' b) r

-- Or equivalently, using FreeT

data FreeF f a b = FP a | FF (f b)

newtype FreeT f m a = FT { runFT :: m (FreeF f a (FreeT f m a)) }

type Proxy7 a' a b' b m r = FreeT (ReqRes a' a b' b) m r
