{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Compiler.Hoopl.Lens where

import Control.Applicative
import Compiler.Hoopl hiding ((<*>))
import Control.Lens
import Data.Foldable

blockNodesOf :: (forall e' x'. Traversal (n1 e' x') (n2 e' x') a b)
             -> Traversal (Block n1 e x) (Block n2 e x) a b
blockNodesOf nodeLens f = go
  where
    go (BlockCC e bl x) =
        BlockCC <$> traverseOf nodeLens f e
                <*> blockNodesOf nodeLens f bl
                <*> traverseOf nodeLens f x

    go (BlockCO e bl) = BlockCO <$> traverseOf nodeLens f e
                                <*> blockNodesOf nodeLens f bl
    go (BlockOC bl x) = BlockOC <$> blockNodesOf nodeLens f bl
                                <*> traverseOf nodeLens f x

    go BNil         = pure BNil
    go (BMiddle n)  = BMiddle <$> traverseOf nodeLens f n
    go (BCat l r)   = BCat <$> go l <*> go r
    go (BSnoc bl n) = BSnoc <$> go bl <*> traverseOf nodeLens f n
    go (BCons n bl) = BCons <$> traverseOf nodeLens f n <*> go bl

traverseMaybeO :: Applicative f => (a -> f b) -> MaybeO e a -> f (MaybeO e b)
traverseMaybeO _ NothingO = pure NothingO
traverseMaybeO f (JustO x) = JustO <$> f x

graphNodesOf :: (NonLocal n1, NonLocal n2)
             => (forall e' x'. Traversal (n1 e' x') (n2 e' x') a b)
             -> Traversal (Graph n1 e x) (Graph n2 e x) a b
graphNodesOf nodeLens f = go
  where
    go GNil               = pure GNil
    go (GUnit bl)         = GUnit <$> blockNodesOf nodeLens f bl
    go (GMany me body mx) = GMany <$> traverseMaybeO (blockNodesOf nodeLens f) me
                                  <*> unwrap_body body
                                  <*> traverseMaybeO (blockNodesOf nodeLens f) mx

    unwrap_body =
        fmap (Data.Foldable.foldr (addBlock . snd) emptyBody)
            . traverse (\(l, x) -> (,) <$> pure l
                                      <*> blockNodesOf nodeLens f x)
            . bodyList
