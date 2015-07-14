{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module PipeCont where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Control.Monad.Trans.State
import Control.Monad.Trans.Free.Church
import Data.Functor.Identity
import qualified Pipes as P
import qualified Pipes.Internal as P
import qualified Pipes.Prelude as P

data ProxyF a' a b' b f
    = Request a' (a  -> f)
    | Respond b  (b' -> f)

newtype Proxy a' a b' b m r = Proxy { runProxy :: FT (ProxyF a' a b' b) m r }

toProxy :: Monad m => Proxy a' a b' b m r -> P.Proxy a' a b' b m r
toProxy (Proxy (FT p)) =
    P.M $ p (return . P.Pure) $ \k x -> case x of
        Request a' fa  -> return $ P.Request a' (P.M . k . fa)
        Respond b  fb' -> return $ P.Respond b  (P.M . k . fb')

fromProxy :: Monad m => P.Proxy a' a b' b m r -> Proxy a' a b' b m r
fromProxy (P.Request a' fa) = Proxy $ FT $ \_ fun ->
    fun return (Request a' (fromProxy . fa))
fromProxy (P.Respond b  fb') = undefined
fromProxy (P.M m) = Proxy $ FT $ \pur fun ->
    m >>= \x -> runFT (runProxy (fromProxy x)) pur fun
fromProxy (P.Pure p) = Proxy $ FT $ \pur _ -> pur p

(>->) :: Monad m
      => Proxy a' a () b m r -> Proxy () b c' c m r -> Proxy a' a c' c m r
Proxy (FT f) >-> Proxy (FT g) = Proxy $ FT $ \pur fun ->
    f pur $ \h p ->
        case p of
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

type Producer b = Proxy P.X () () b -- Defined in ‘Pipes.Core’

fold :: forall a b x m. Monad m
     => (x -> a -> x) -> x -> (x -> b) -> Producer a m () -> m b
fold step begin done (toProxy -> p) = P.fold step begin done p

toListM :: Monad m => Producer a m () -> m [a]
toListM = fold step begin done
  where
    step x a = x . (a:)
    begin = id
    done x = x []

runEffect :: Monad m => Proxy P.X () () P.X m r -> m r
runEffect (Proxy p) = undefined
