{-# LANGUAGE
    DataKinds
  , GADTs
  , RankNTypes
  , TypeFamilies
  #-}

module Ximin where

data Tree a = TLeaf | TNode a (Tree a) (Tree a)

data HTree xs where
  HLeaf :: HTree 'TLeaf
  HNode :: x -> HTree ls -> HTree rs -> HTree ('TNode x ls rs)

type family TreeMap (f :: * -> *) (t :: Tree *) :: Tree * where
    TreeMap f 'TLeaf = 'TLeaf
    TreeMap f ('TNode x l r) = 'TNode (f x) (TreeMap f l) (TreeMap f r)

htreeMap :: forall (f :: * -> *) xs. (forall x. x -> f x) -> HTree xs -> HTree (TreeMap f xs)
htreeMap _ HLeaf = HLeaf
htreeMap k (HNode x l r) = HNode (k x) (htreeMap k l) (htreeMap k r)
