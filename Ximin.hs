{-# LANGUAGE
    DataKinds
  , ConstraintKinds
  , GADTs
  , RankNTypes
  , TypeApplications
  , TypeFamilies
  , ScopedTypeVariables
  #-}

module Ximin where

import Data.Constraint

data Tree a = TLeaf | TNode a (Tree a) (Tree a)

data HTree xs where
  HLeaf :: HTree 'TLeaf
  HNode :: x -> HTree ls -> HTree rs -> HTree ('TNode x ls rs)

class Mapped x where
    type Result x :: *

instance Mapped Int where
    type Result Int = Integer
instance Mapped Float where
    type Result Float = Double

type family TreeMapped (t :: Tree *) :: Tree * where
  TreeMapped 'TLeaf = 'TLeaf
  TreeMapped ('TNode x l r) = 'TNode (Result x) (TreeMapped l) (TreeMapped r)

htreeMap :: forall xs. (forall x. x -> Result x) -> HTree xs -> HTree (TreeMapped xs)
htreeMap _ HLeaf = HLeaf
htreeMap k (HNode x l r) = HNode (k x) (htreeMap k l) (htreeMap k r)

sample
    :: HTree ('TNode Int ('TNode Float 'TLeaf 'TLeaf) ('TNode Float 'TLeaf 'TLeaf))
    -> HTree ('TNode Integer ('TNode Double 'TLeaf 'TLeaf) ('TNode Double 'TLeaf 'TLeaf))
sample = htreeMap _
