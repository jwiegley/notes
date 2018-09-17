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

import Data.Constraint

main :: IO ()
main = return ()

data Tree a = TLeaf | TNode a (Tree a) (Tree a)

data HTree xs where
  HLeaf :: HTree 'TLeaf
  HNode :: x -> HTree ls -> HTree rs -> HTree ('TNode x ls rs)

-- This type constraint observes which type occurs at each node.
type family Observe (xs :: k) (x :: *) :: Constraint where
    Observe 'TLeaf x = x ~ x
    Observe ('TNode x ls rs) y = (Observe ls x, Observe rs x, x ~ y)

-- This type function substitutes the type indices at nodes in a tree.
type family Subst (xs :: k) (y :: *) :: k where
    Subst 'TLeaf _ = 'TLeaf
    Subst ('TNode _ lxs rxs) y =
        'TNode y (Subst lxs y) (Subst rxs y)

treeFold :: forall x y xs. Observe xs x => (x -> y) -> HTree xs -> HTree (Subst xs y)
treeFold f HLeaf = HLeaf
treeFold f (HNode x l r) = HNode (f x) (treeFold f l) (treeFold f r)