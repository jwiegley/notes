{-# LANGUAGE RankNTypes #-}

module Pipes.Lens where

import           Control.Applicative
import qualified Control.Foldl as F
import           Control.Lens hiding (each)
import           Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import           Data.Monoid (Monoid(..))
import           Pipes
import           Pipes.Group
import qualified Pipes.Prelude as P

foldOver :: Monad m => Fold s a -> s -> Producer a m ()
foldOver t x = each (x ^.. t)

foldBy :: Monad m => Fold s a -> Pipe s a m ()
foldBy t = await >>= \x -> each (x ^.. t)

foldMap :: (Monoid b, Monad m) => (a -> b) -> Producer a m () -> m b
foldMap = F.purely P.fold . flip F.foldMap id

mconcat :: (Monoid a, Monad m) => Producer a m () -> m a
mconcat = F.purely P.fold F.mconcat

unfold :: Monad m => (b -> Maybe (a, b)) -> b -> Producer a m b
unfold = undefined

enumFromTo :: (Monad m, Enum a, Ord a) => a -> a -> Producer a m ()
enumFromTo = undefined

iterate :: Monad m => (a -> a) -> a -> Producer a m ()
iterate = undefined

repeat :: Monad m => a -> Producer a m ()
repeat = undefined

replicate :: Monad m => Int -> a -> Producer a m ()
replicate = undefined

chunksOfBs :: Traversal' BL.ByteString B.ByteString
chunksOfBs f bl = BL.fromChunks <$> traverse f (BL.toChunks bl)

-- dropElem :: Monad m => Traversal' a b -> Int -> Pipe a a m ()
-- dropElem t = loop
--   where
--     loop n = do
--         x <- await
--         if n <= 0
--             then yield x
--             else undefined

-- filterElem :: Monad m => Fold s a -> (a -> Bool) -> Pipe s s m ()
-- filterElem t p = do
--     s <- await
--     yield $ s ^. droppingWhile p t
