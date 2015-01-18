{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Language.Tempest.GraphWrapper where

import Control.Applicative
import Compiler.Hoopl hiding ((<*>))
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Language.Tempest.IR as IR

-- All of the code below is pure boilerplate, so we can use 'Foldable' and
-- 'Traversable' with Hoopl Graphs over our 'Node a' type.

newtype NodeWrap v e x a = NodeWrap { getNodeWrap :: Node a v e x }

instance Functor (NodeWrap v e x) where
    fmap f (NodeWrap (Node instr meta)) = NodeWrap (Node instr (f meta))

instance Foldable (NodeWrap v e x) where
    foldMap f (NodeWrap (Node _instr meta)) = f meta

instance Traversable (NodeWrap v e x) where
    sequenceA (NodeWrap (Node instr meta)) = NodeWrap . Node instr <$> meta

newtype BlockWrap v e x a = BlockWrap { getBlockWrap :: Block (Node a v) e x }

instance Functor (BlockWrap v e x) where
    fmap f (BlockWrap b) =
        BlockWrap (mapBlock (getNodeWrap . fmap f . NodeWrap) b)

instance Foldable (BlockWrap v C C) where
    foldMap f (BlockWrap b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest) )
            b mempty

instance Foldable (BlockWrap v C O) where
    foldMap f (BlockWrap b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest) )
            b mempty

instance Foldable (BlockWrap v O C) where
    foldMap f (BlockWrap b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest) )
            b mempty

instance Foldable (BlockWrap v O O) where
    foldMap f (BlockWrap b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest)
            , (\node rest -> foldMap f (NodeWrap node) <> rest) )
            b mempty

instance Traversable (BlockWrap v C C) where
    sequenceA (BlockWrap b) = BlockWrap <$> go b
      where
        go :: Applicative m
           => Block (Node (m a) v) C C -> m (Block (Node a v) C C)
        go (BlockCC e bl x) =
            BlockCC <$> (getNodeWrap <$> sequenceA (NodeWrap e))
                    <*> (getBlockWrap <$> sequenceA (BlockWrap bl))
                    <*> (getNodeWrap <$> sequenceA (NodeWrap x))

instance Traversable (BlockWrap v C O) where
    sequenceA (BlockWrap b) = BlockWrap <$> go b
      where
        go :: Applicative m
           => Block (Node (m a) v) C O -> m (Block (Node a v) C O)
        go (BlockCO e bl)   =
            BlockCO <$> (getNodeWrap <$> sequenceA (NodeWrap e))
                    <*> (getBlockWrap <$> sequenceA (BlockWrap bl))

instance Traversable (BlockWrap v O C) where
    sequenceA (BlockWrap b) = BlockWrap <$> go b
      where
        go :: Applicative m
           => Block (Node (m a) v) O C -> m (Block (Node a v) O C)
        go (BlockOC bl x) =
            BlockOC <$> (getBlockWrap <$> sequenceA (BlockWrap bl))
                    <*> (getNodeWrap <$> sequenceA (NodeWrap x))

instance Traversable (BlockWrap v O O) where
    sequenceA (BlockWrap b) = BlockWrap <$> go b
      where
        go :: Applicative m
           => Block (Node (m a) v) O O -> m (Block (Node a v) O O)
        go BNil         = pure BNil
        go (BMiddle n)  = BMiddle . getNodeWrap <$> sequenceA (NodeWrap n)
        go (BCat l r)   = BCat <$> (getBlockWrap <$> sequenceA (BlockWrap l))
                               <*> (getBlockWrap <$> sequenceA (BlockWrap r))
        go (BSnoc bl n) = BSnoc <$> (getBlockWrap <$> sequenceA (BlockWrap bl))
                                <*> (getNodeWrap <$> sequenceA (NodeWrap n))
        go (BCons n bl) = BCons <$> (getNodeWrap <$> sequenceA (NodeWrap n))
                                <*> (getBlockWrap <$> sequenceA (BlockWrap bl))

newtype GraphWrap v e x a =
    GraphWrap { getGraphWrap :: Graph (Node a v) e x }

instance Functor (GraphWrap v e x) where
    fmap f (GraphWrap g) =
        GraphWrap (mapGraph (getNodeWrap . fmap f . NodeWrap) g)

instance Foldable (GraphWrap v e x) where
    foldMap f (GraphWrap g) =
        foldGraphNodes (\node rest -> foldMap f (NodeWrap node) <> rest)
                       g mempty

instance Foldable (MaybeO e) where
    foldMap _ NothingO = mempty
    foldMap f (JustO x) = f x

instance Traversable (MaybeO e) where
    sequenceA NothingO = pure NothingO
    sequenceA (JustO x) = JustO <$> x

instance Traversable (GraphWrap v e x) where
    sequenceA (GraphWrap g) = GraphWrap <$> go g
      where
        go :: Applicative m
           => Graph (Node (m a) v) e x -> m (Graph (Node a v) e x)
        go GNil       = pure GNil
        go (GUnit bl) = GUnit <$> (getBlockWrap <$> sequenceA (BlockWrap bl))
        go (GMany me body mx) =
            GMany <$> unwrap_e me
                  <*> unwrap_body body
                  <*> unwrap_x mx
          where
            wrapUnwrapCC :: Applicative m
                         => Block (Node (m a) v) C C -> m (Block (Node a v) C C)
            wrapUnwrapCC = fmap getBlockWrap . sequenceA . BlockWrap

            wrapUnwrapOC :: Applicative m
                         => Block (Node (m a) v) O C -> m (Block (Node a v) O C)
            wrapUnwrapOC = fmap getBlockWrap . sequenceA . BlockWrap

            wrapUnwrapCO :: Applicative m
                         => Block (Node (m a) v) C O -> m (Block (Node a v) C O)
            wrapUnwrapCO = fmap getBlockWrap . sequenceA . BlockWrap

            unwrap_e :: Applicative m
                     => MaybeO e (Block (Node (m a) v) O C)
                     -> m (MaybeO e (Block (Node a v) O C))
            unwrap_e = sequenceA . fmap wrapUnwrapOC

            unwrap_x :: Applicative m
                     => MaybeO x (Block (Node (m a) v) C O)
                     -> m (MaybeO x (Block (Node a v) C O))
            unwrap_x = sequenceA . fmap wrapUnwrapCO

            unwrap_body :: Applicative m
                        => Body (Node (m a) v) -> m (Body (Node a v))
            unwrap_body =
                -- jww (2015-01-15): Is this the right way to tear down a
                -- 'LabelMap' and build it back up?
                fmap (Data.Foldable.foldr
                         (\x rest -> addBlock (snd x) rest) emptyBody)
                    . sequenceA
                    . fmap (sequenceA . fmap wrapUnwrapCC)
                    . bodyList

newtype IRInstrWrap e x v = IRInstrWrap { getIRInstrWrap :: IRInstr v e x }

instance Functor (IRInstrWrap e x) where
    fmap f (IRInstrWrap m) = IRInstrWrap (go m)
      where
        go (Label x)                     = Label x
        go (Alloc ag msrc dst)           = Alloc ag (f <$> msrc) (f dst)
        go (Reclaim src)                 = Reclaim (f src)
        go (Instr i)                     = Instr (fmap f i)
        go (LoadConst c dst)             = LoadConst c (f dst)
        go (Move src dst)                = Move (f src) (f dst)
        go (Copy src dst)                = Copy (f src) (f dst)
        go (Save lin src x)              = Save lin (f src) x
        go (Restore x1 x2 dst)           = Restore x1 x2 (f dst)
        go (SaveOffset lin off src x)    = SaveOffset lin off (f src) x
        go (RestoreOffset lin off x dst) = RestoreOffset lin off x (f dst)
        go (Jump x)                      = Jump x
        go (Branch x1 cond x2 x3)        = Branch x1 (f cond) x2 x3
        go (IR.Stwb x1 src dst x2 x3)    = IR.Stwb x1 (f src) (f dst) x2 x3
        go (IR.Strb src dst x2 x3)       = IR.Strb (f src) (f dst) x2 x3
        go (IR.Call cc i)                = IR.Call cc (fmap f i)
        go (ReturnInstr liveInRegs i)    = ReturnInstr liveInRegs (fmap f i)

newtype NodeWrapVar a e x v = NodeWrapVar { getNodeWrapVar :: Node a v e x }

instance Functor (NodeWrapVar v e x) where
    fmap f (NodeWrapVar (Node instr meta)) =
        NodeWrapVar (Node (getIRInstrWrap . fmap f . IRInstrWrap $ instr) meta)
