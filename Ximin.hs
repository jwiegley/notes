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

class Z ys xs where
  z :: HTree ys -> HTree xs
instance Z 'TLeaf 'TLeaf where
  z HLeaf = HLeaf
instance (Z lys ls, Z rys rs) => Z ('TNode y lys rys) ('TNode x ls rs) where
  z (HNode _y ls rs) = HNode undefined (z ls) (z rs)

class ZZ xs ys where
    structuralEquality :: Dict (xs ~ ys)

instance ZZ 'TLeaf 'TLeaf where
    structuralEquality = Dict

instance (ZZ lxs lys, ZZ rxs rys) => ZZ ('TNode x lxs rxs) ('TNode y lys rys) where
    structuralEquality =
        withDict (structuralEquality :: Dict (lxs ~ lys)) $
        withDict (structuralEquality :: Dict (rxs ~ rys)) $
        withDict (error "Nodes are not equal, this is a lie!" :: Dict (x ~ y)) $
        Dict

zz :: forall xs ys. ZZ xs ys => HTree ys -> HTree xs
zz HLeaf = withDict (structuralEquality :: Dict (xs ~ ys)) HLeaf
  -- ys ~ 'TLeaf by GADT, compiler knows this, as evidenced by the error message
  -- then SameStruct xs ys, by constraint, compiler also knows this, as evidenced by the error message
  -- the only xs that satisfies (SameStruct 'TLeaf *) is 'TLeaf,
  -- ^ the compiler "should" know this?
  -- QED?
zz (HNode _y ls rs) = withDict (structuralEquality :: Dict (xs ~ ys)) $ HNode undefined ls rs

