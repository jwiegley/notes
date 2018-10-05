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

import Data.Void

data Tree a = TLeaf | TNode a (Tree a) (Tree a)

data HTree xs where
  HLeaf :: HTree 'TLeaf
  HNode :: x -> HTree ls -> HTree rs -> HTree ('TNode x ls rs)

type family TreeMapped (f :: * -> *) (t :: Tree *) :: Tree * where
  TreeMapped _ 'TLeaf = 'TLeaf
  TreeMapped f ('TNode x l r) = 'TNode (f x) (TreeMapped f l) (TreeMapped f r)

type family Function (f :: * -> *) (t :: Tree *) :: * where
  Function _ 'TLeaf = Void -> Void
  Function f ('TNode x l r) = (x -> f x, Function f l, Function f r)

type family Result x :: *

type instance Result Int   = Integer
type instance Result Float = Double

htreeMap :: forall xs. HTree xs -> Function Result xs -> HTree (TreeMapped Result xs)
htreeMap HLeaf _ = HLeaf
htreeMap (HNode x l r) (k, kl, kr) = HNode (k x) (htreeMap l kl) (htreeMap r kr)

sample
    :: HTree ('TNode Int     ('TNode Float  'TLeaf 'TLeaf)
                            ('TNode Float  'TLeaf 'TLeaf))
    -> HTree ('TNode Integer ('TNode Double 'TLeaf 'TLeaf)
                            ('TNode Double 'TLeaf 'TLeaf))
sample = flip htreeMap
  (toInteger,
   (fromRational . toRational, id, id),
   (fromRational . toRational, id, id))

{-
type family Expose (xs :: k) :: *

type instance Expose 'TLeaf = Void
type instance Expose ('TNode x _ _) = x

-- This type constraint observes which type occurs at each node.
type family Observe (xs :: k) (x :: *) :: Constraint

type instance Observe 'TLeaf x = x ~ x
type instance Observe ('TNode x ls rs) y = (Observe ls x, Observe rs x, x ~ y)

-- This type function substitutes the type indices at nodes in a tree.
type family Subst (xs :: k) (y :: *) :: k

type instance Subst 'TLeaf _ = 'TLeaf
type instance Subst ('TNode _ lxs rxs) y = 'TNode y (Subst lxs y) (Subst rxs y)

fromHTree :: HTree xs -> HHTree (Expose xs) xs
fromHTree HLeaf = HHLeaf
fromHTree (HNode x l r) = HHNode x (fromHTree l) (fromHTree r)

treeFold :: forall xs ys. (Expose xs -> Expose ys) -> HTree xs -> HTree ys
treeFold f HLeaf = HLeaf
treeFold f (HNode x l r) = HNode (f x) (treeFold f l) (treeFold f r)
-}
