{-# LANGUAGE
    DataKinds
  , FlexibleContexts
  , FlexibleInstances
  , GADTs
  , MultiParamTypeClasses
  , PolyKinds
  , TypeFamilies
  , ScopedTypeVariables
  #-}

module Ximin (TTraversable(..), treeFold, treeFoldA) where

import Data.Constraint

data Tree a = TLeaf | TNode a (Tree a) (Tree a)

data HTree xs where
  HLeaf :: HTree 'TLeaf
  HNode :: x -> HTree ls -> HTree rs -> HTree ('TNode x ls rs)

-- This type constraint observes which type occurs at each node.
type family Observe (xs :: k) (x :: *) :: Constraint

type instance Observe 'TLeaf x = x ~ x
type instance Observe ('TNode x ls rs) y = (Observe ls x, Observe rs x, x ~ y)

-- This type function substitutes the type indices at nodes in a tree.
type family Subst (xs :: k) (y :: *) :: k

type instance Subst 'TLeaf _ = 'TLeaf
type instance Subst ('TNode _ lxs rxs) y = 'TNode y (Subst lxs y) (Subst rxs y)

treeFold :: forall x y xs. Observe xs x => (x -> y) -> HTree xs -> HTree (Subst xs y)
treeFold _ HLeaf = HLeaf
treeFold f (HNode x l r) = HNode (f x) (treeFold f l) (treeFold f r)

treeFoldA :: forall x m y xs. (Applicative m, Observe xs x)
    => (x -> m y) -> HTree xs -> m (HTree (Subst xs y))
treeFoldA _ HLeaf = pure HLeaf
treeFoldA f (HNode x l r) = HNode <$> f x <*> treeFoldA f l <*> treeFoldA f r

class TTraversable t where
    ttraverse
        :: (Observe a x, Applicative f)
        => (x -> f y)
        -> t a
        -> f (t (Subst a y))

instance TTraversable HTree where
    ttraverse = treeFoldA