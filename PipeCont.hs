{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module PipeCont where

import           Control.Applicative
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Free.Church
import qualified Data.Foldable as F
import qualified Pipes as P
import qualified Pipes.Internal as P
import qualified Pipes.Prelude as P

data ProxyF a' a b' b f
    = Request a' (a  -> f)
    | Respond b  (b' -> f) deriving Functor

newtype Proxy a' a b' b m r = Proxy { runProxy :: FT (ProxyF a' a b' b) m r }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadFree (ProxyF a' a b' b))

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
