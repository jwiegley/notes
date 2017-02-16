{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module PipeCont where

import           Control.Applicative
import           Control.Exception.Lifted
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Cont
import           Control.Monad.Trans.Control
import           Control.Monad.Trans.Free.Church
import qualified Data.Conduit.Internal as C
import qualified Data.Foldable as F
import           Data.Functor
import           Data.Void
import           GHC.Prim
import qualified Pipes as P
import qualified Pipes.Internal as P
import qualified Pipes.Prelude as P

data ProxyF a' a b' b f
    = Request a' (a  -> f)
    | Respond b  (b' -> f) deriving Functor

newtype Proxy a' a b' b m r = Proxy { runProxy :: FT (ProxyF a' a b' b) m r }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadFree (ProxyF a' a b' b))

-- instance PipeLike (Proxy a' a b' b m) where
--     type Repr (Proxy a' a b' b m) = Codensity m
--     proxy req res = undefined

toProxy :: Monad m => Proxy a' a b' b m r -> P.Proxy a' a b' b m r
toProxy (Proxy (FT p)) = P.M $ p (return . P.Pure) $ \k -> \case
    Request a' fa  -> return $ P.Request a' (P.M . k . fa)
    Respond b  fb' -> return $ P.Respond b  (P.M . k . fb')

fromProxy :: Monad m => P.Proxy a' a b' b m r -> Proxy a' a b' b m r
fromProxy p = Proxy $ FT $ \pur fun ->
    let go x = runFT (runProxy (fromProxy x)) pur fun in
    case p of
        P.Request a' fa  -> fun go (Request a' fa)
        P.Respond b  fb' -> fun go (Respond b  fb')
        P.M       m      -> m >>= go
        P.Pure    r      -> pur r

(>->) :: Monad m
      => Proxy a' a () b m r -> Proxy () b c' c m r -> Proxy a' a c' c m r
Proxy (FT f) >-> Proxy (FT g) = Proxy $ FT $ \pur fun ->
    f pur $ \h -> \case
        Request a' fa  -> fun h (Request a' fa)
        Respond b  fb' -> do
            g pur $ \k p' ->
                case p' of
                    Request () fb  -> k (fb b)
                    Respond c  fc' -> fun k (Respond c fc')
            h (fb' ())

newtype GProxy a b m r =
    GProxy { runGProxy :: forall s.
                         ((a -> m s) -> m s)
                       -> (b -> m s -> m s)
                       -> (r -> m s)
                       -> m s }

class Stream (p :: k) where
    data StreamRepr p a b (m :: * -> *) r :: *
    getStream :: Monad m => StreamRepr p a b m r -> GProxy a b m r
    makeStream :: Monad m => GProxy a b m r -> StreamRepr p a b m r

liftProxy :: Monad m => P.Proxy a' a () b m r -> GProxy a b m r
liftProxy p = GProxy $ \req res pur -> case p of
    P.Request _a' fa  -> req $ \a -> runGProxy (liftProxy (fa  a)) req res pur
    P.Respond b   fb' -> res b (runGProxy (liftProxy (fb' ())) req res pur)
    P.M       m      -> m >>= \p' -> runGProxy (liftProxy p') req res pur
    P.Pure    r      -> pur r

lowerProxy :: Monad m => GProxy a b m r -> P.Proxy () a () b m r
lowerProxy (GProxy p) = P.M $ p req res (return . P.Pure)
  where
    req k = return $ P.Request () (P.M . k)
    res b next = return $ P.Respond b (\_ -> P.M next)

instance Stream P.Proxy where
    newtype StreamRepr P.Proxy a b m r = ProxyStream (P.Proxy () a () b m r)
    getStream (ProxyStream p) = liftProxy p
    makeStream = ProxyStream . lowerProxy

liftPipe :: MonadBaseControl IO m => C.Pipe l i o u m r -> GProxy i o m r
liftPipe p = GProxy $ \req res pur -> case p of
    C.HaveOutput c fin o ->
        res o (runGProxy (liftPipe c) req res pur `finally` fin)
    C.NeedInput k _h -> req $ \i -> runGProxy (liftPipe (k i)) req res pur
    C.Done r         -> pur r
    C.PipeM m        -> m >>= \c' -> runGProxy (liftPipe c') req res pur
    C.Leftover c _l  -> runGProxy (liftPipe c) req res pur

lowerPipe :: Monad m => GProxy i o m r -> C.Pipe Void i o Void m r
lowerPipe (GProxy p) = C.PipeM $ p req res (return . C.Done)
  where
    req k = return $ C.NeedInput (C.PipeM . k) absurd
    res b next = return $ C.HaveOutput (C.PipeM next) (return ()) b

instance Stream C.Pipe where
    newtype StreamRepr C.Pipe a b m r = ConduitStream (C.Pipe Void a b Void m r)
    getStream (ConduitStream c) = undefined -- liftPipe c
    makeStream = ConduitStream . lowerPipe

(>-->) :: (MonadBaseControl IO m, Functor m, Stream pipe)
       => StreamRepr pipe a b m r -> StreamRepr pipe b c m r
       -> StreamRepr pipe a c m r
f >--> g = makeStream $ GProxy $ \req res pur ->
    runGProxy (getStream f) req
        (\b next -> runGProxy (getStream g) (\k -> k b) res pur >> next) pur

(<-<) :: Monad m
      => Proxy () b c' c m r -> Proxy a' a () b m r -> Proxy a' a c' c m r
(<-<) = flip (>->)

type Effect      = Proxy P.X () () P.X
type Producer b  = Proxy P.X () () b
type Pipe a b    = Proxy () a () b
type Consumer a  = Proxy () a () P.X
type Client a' a = Proxy a' a () P.X
type Server b' b = Proxy P.X () b' b

type Effect' m r      = forall x' x y' y . Proxy x' x y' y m r
type Producer' b m r  = forall x' x . Proxy x' x () b m r
type Consumer' a m r  = forall y' y . Proxy () a y' y m r
type Server' b' b m r = forall x' x . Proxy x' x b' b m r
type Client' a' a m r = forall y' y . Proxy a' a y' y m r

fold :: forall a b x m. Monad m
     => (x -> a -> x) -> x -> (x -> b) -> Producer a m () -> m b
fold step begin done (toProxy -> p) = P.fold step begin done p

toListM :: Monad m => Producer a m () -> m [a]
toListM = fold step begin done
  where
    step x a = x . (a:)
    begin = id
    done x = x []

runEffect :: Monad m => Effect m r -> m r
runEffect (Proxy (FT f)) = f return $ \k -> \case
    Request _ fu -> k (fu ())
    Respond _ fu -> k (fu ())

respond :: Monad m => a -> Proxy x' x a' a m a'
respond a = liftF $ Respond a id

request :: Monad m => a' -> Proxy a' a y' y m a
request a' = liftF $ Request a' id

(//>)
    :: Monad m
    =>       Proxy x' x b' b m a'
    -- ^
    -> (b -> Proxy x' x c' c m b')
    -- ^
    ->       Proxy x' x c' c m a'
    -- ^
Proxy (FT p0) //> fb = Proxy $ FT $ \pur fun -> p0 pur $ \k -> \case
    Request x' fx  -> fun k (Request x' fx)
    Respond b  fb' -> runFT (runProxy (fb b)) (k . fb') fun

for :: Monad m
    =>       Proxy x' x b' b m a'
    -- ^
    -> (b -> Proxy x' x c' c m b')
    -- ^
    ->       Proxy x' x c' c m a'
for = (//>)

yield :: Monad m => a -> Producer' a m ()
yield = respond

each :: (Monad m, F.Foldable f) => f a -> Producer' a m ()
each = F.foldr (\a p -> yield a >> p) (return ())

main :: IO ()
main = do
    let p = for (each [(1 :: Int)..10]) $ \x -> liftIO $ print x
    runEffect (p :: Effect IO ())
