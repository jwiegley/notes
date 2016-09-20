{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module PipesCompile where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.Trans.Class
import qualified Data.Foldable as F
import           Debug.Trace
import           Pipes (X)
import qualified Pipes as P
import qualified Pipes.Internal as P
import qualified Pipes.Prelude as P
import           Prelude hiding (map)

-- | The simplest expression of 'pipes' is a two term, get/put algebra,
--   enriched with the ability to interleave effects using FreeT.
data CmdF a' a b' b m r
    = Get a' (a  -> r)
    | Put b  (b' -> r)
    | M      (m r)
    deriving Functor

instance MonadTrans (CmdF a' a b' b) where
    lift = M

newtype Cmd a' a b' b m r = Cmd { runCmd :: Free (CmdF a' a b' b m) r }

instance Monad m => Functor (Cmd a' a b' b m) where
    fmap f (Cmd p0) = Cmd $ go p0 where
        go = \case
            Free (Get a' fa)  -> Free $ Get a' (\a  -> go (fa  a ))
            Free (Put b  fb') -> Free $ Put b  (\b' -> go (fb' b'))
            Free (M   m)      -> Free $ M (m >>= \p' -> return (go p'))
            Pure      r       -> Pure (f r)

instance Monad m => Applicative (Cmd a' a b' b m) where
    pure      = Cmd . Pure
    Cmd pf <*> Cmd px = Cmd $ go pf
      where
        go = \case
            Free (Get a' fa)  -> Free $ Get a' (\a  -> go (fa  a ))
            Free (Put b  fb') -> Free $ Put b  (\b' -> go (fb' b'))
            Free (M   m)      -> Free $ M (m >>= \p' -> return (go p'))
            Pure      f       -> fmap f px
    m *> k = m >>= (\_ -> k)

instance Monad m => Monad (Cmd a' a b' b m) where
    return = pure
    (>>=)  = _bind

_bind :: Monad m
      => Cmd a' a b' b m r -> (r -> Cmd a' a b' b m r') -> Cmd a' a b' b m r'
Cmd p0 `_bind` f = Cmd $ go p0
  where
    go = \case
        Free (Get a' fa)  -> Free $ Get a' (\a  -> go (fa  a ))
        Free (Put b  fb') -> Free $ Put b  (\b' -> go (fb' b'))
        Free (M m)        -> Free $ M (merge m)
        Pure    r         -> runCmd $ f r
      where
        -- Merge M actions in the base monad.
        merge m = m >>= \case
            Free (M m') -> merge m'
            p' -> case go p' of
                Free (M m') -> m'
                p'' -> return p''

instance MonadTrans (Cmd a' a b' b) where
    lift m = Cmd $ Free $ M (fmap Pure m)

-- | We use this simple representation as a shallow syntactic form over the
--   deeper pipes embedding, 'Pipes.Internal.CmdF'. The advantage of
--   separating between shallow and deep is that it allows us to encode fusion
--   during pipeline construction, allowing for the fastest possible execution
--   without relying on rewrite rules. See the paper
--   http://www.cse.chalmers.se/~emax/documents/svenningsson2013combining.pdf
--   for a full description of this technique, and other applications.
class Syntactic a where
    type Internal a
    fromSyntax :: a -> Internal a
    toSyntax   :: Internal a -> a

instance Monad m => Syntactic (Cmd a' a b' b m r) where
    type Internal (Cmd a' a b' b m r) = P.Proxy a' a b' b m r
    fromSyntax = iterM (\case Get a' fa  -> P.Request a' fa
                              Put b  fb' -> P.Respond b  fb'
                              M m        -> P.M m) . runCmd
    toSyntax p = Cmd $ case p of
        P.Request a' fa  -> Free $ Get a' (\a  -> runCmd $ toSyntax $ fa  a)
        P.Respond b  fb' -> Free $ Put b  (\b' -> runCmd $ toSyntax $ fb' b')
        P.M m            -> Free $ M (fmap (runCmd . toSyntax) m)
        P.Pure x         -> Pure x

type Producer b m = Cmd X () () b m
type Consumer a   = Cmd () a () X
type Effect m     = Cmd X () () X m
type Pipe a b     = Cmd () a () b

type Producer' b m r = forall x' x. Cmd x' x () b m r
type Consumer' a m r = forall y' y. Cmd () a y' y m r

yield :: Monad m => a -> Producer' a m ()
yield x = Cmd $ Free $ Put x Pure

await :: Monad m => Consumer' a m a
await = Cmd $ Free $ Get () Pure

(//>) :: Monad m
    => Cmd x' x b' b m a' -> (b -> Cmd x' x c' c m b')
    -> Cmd x' x c' c m a'
Cmd inc //> k = Cmd $ go inc
  where
    go = \case
        Free (Get x' fx)  -> Free $ Get x' (\x -> go (fx x))
        Free (Put b  fb') -> runCmd $ k b >>= \b' -> Cmd $ go (fb' b')
        Free (M m)        -> Free (M (m >>= \p' -> return (go p')))
        Pure a'           -> Pure a'

for :: Monad m
    => Cmd x' x b' b m a' -> (b -> Cmd x' x c' c m b')
    -> Cmd x' x c' c m a'
for = (//>)

(>->) :: Monad m
      => Cmd a' a () b m r
      -> Cmd () b c' c m r
      -> Cmd a' a c' c m r
p1 >-> p2 = (\() -> p1) +>> p2

(>>~) :: Monad m
      =>       Cmd a' a b' b m r
      -> (b -> Cmd b' b c' c m r)
      ->       Cmd a' a c' c m r
Cmd p >>~ fb = Cmd $ case p of
    Free (Get a' fa)  -> Free $ Get a' (\a -> runCmd $ Cmd (fa a) >>~ fb)
    Free (Put b  fb') -> runCmd $ (Cmd . fb') +>> fb b
    Free (M m)        -> Free (M (m >>= \p' -> return (runCmd (Cmd p' >>~ fb))))
    Pure r            -> Pure r

(+>>) :: Monad m
      => (b' -> Cmd a' a b' b m r)
      ->        Cmd b' b c' c m r
      ->        Cmd a' a c' c m r
fb' +>> Cmd p = Cmd $ case p of
    Free (Get b' fb)  -> runCmd $ fb' b' >>~ (Cmd . fb)
    Free (Put c  fc') -> Free $ Put c (\c' -> runCmd $ fb' +>> Cmd (fc' c'))
    Free (M m)        ->
        Free (M (m >>= \p' -> return (runCmd (fb' +>> Cmd p'))))
    Pure r            -> Pure r

foldLog :: Monad m => (x -> a -> x) -> x -> (x -> b) -> P.Producer a m () -> m b
foldLog step begin done p0 = go p0 begin
  where
    go p x = case p of
        P.Request v  _  -> trace "Request" $ P.closed v
        P.Respond a  fu -> trace "Respond" $ go (fu ()) $! step x a
        P.M          m  -> trace "M" $ m >>= \p' -> go p' x
        P.Pure    _     -> trace "Pure" $ return (done x)

toListMLog :: Monad m => P.Producer a m () -> m [a]
toListMLog = foldLog step begin done
  where
    step x a = x . (a:)
    begin = id
    done x = x []

each :: (Monad m, Foldable f) => f a -> Producer' a m ()
each = F.foldr (\a p -> yield a >> p) (return ())

runEffectLog :: Monad m => P.Effect m r -> m r
runEffectLog = go
  where
    go = \case
        P.Request v _ -> trace "Request" $ P.closed v
        P.Respond v _ -> trace "Respond" $ P.closed v
        P.M       m   -> trace "M" $ m >>= go
        P.Pure    r   -> trace "Pure" $ return r

pull :: Monad m => a' -> Cmd a' a a' a m r
pull = go
  where
    go a' = Cmd $ Free $ Get a' (\a -> Free $ Put a (runCmd . go))

cat :: Monad m => Pipe a a m r
cat = pull ()

map :: Monad m => (a -> b) -> Pipe a b m r
map f = for cat (\a -> yield (f a))

main :: IO ()
main = do
    let l = [1..3] :: [Int]

    print "old school:"
    xs <- toListMLog $
        P.for (P.each l) P.yield P.>-> P.map (+1)
    print xs

    print "new school:"
    ys <- toListMLog $ fromSyntax $
        for (each l) yield >-> map (+1)
    print ys

    print "old school:"
    runEffectLog $
        P.for (P.each l) (lift . print)

    print "new school:"
    runEffectLog $ fromSyntax $
        for (each l) (lift . print)
