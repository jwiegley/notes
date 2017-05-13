{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

{-# OPTIONS_GHC -Wall #-}

module MyCat where

import Prelude hiding (id, (.), curry, uncurry, const)

import ConCat.Category
import ConCat.Rep

newtype MyCat a b = MyCat (a -> b)

instance Category MyCat where
    id  = MyCat id
    MyCat f . MyCat g = MyCat (f . g)

instance ProductCat MyCat where
    exl = MyCat fst
    exr = MyCat snd
    MyCat f &&& MyCat g = MyCat (f &&& g)

instance TerminalCat MyCat where
    it = MyCat (\_ -> ())

instance ConstCat MyCat b where
    const b = MyCat (\_ -> b)

instance BottomCat MyCat a b where
    bottomC = MyCat undefined

instance UnknownCat MyCat a b where
    unknownC = MyCat (error "unknown")

instance ClosedCat MyCat where
    curry   (MyCat f) = MyCat (curry f)
    uncurry (MyCat f) = MyCat (uncurry f)

instance CoproductCat MyCat where
    inl = MyCat Left
    inr = MyCat Right
    MyCat f ||| MyCat g = MyCat (f ||| g)

instance Eq a => EqCat MyCat a where
    equal    = MyCat (uncurry (==))
    notEqual = MyCat (uncurry (/=))

instance Ord a => OrdCat MyCat a where
    lessThan           = MyCat (uncurry (<))
    greaterThan        = MyCat (uncurry (>))
    lessThanOrEqual    = MyCat (uncurry (<=))
    greaterThanOrEqual = MyCat (uncurry (<=))

instance Fractional a => FractionalCat MyCat a where
    recipC = MyCat recip
    divideC = MyCat (uncurry (/))

instance (RealFrac a, Integral b) => RealFracCat MyCat a b where
    floorC = MyCat floor
    ceilingC = MyCat ceiling

instance Floating a => FloatingCat MyCat a where
    expC = MyCat exp
    cosC = MyCat cos
    sinC = MyCat sin

instance (Integral a, Num b) => FromIntegralCat MyCat a b where
    fromIntegralC = MyCat fromIntegral

instance DistribCat MyCat where
    distl = MyCat $ \(x, e) -> case e of
        Left y  -> Left (x, y)
        Right z -> Right (x, z)
    distr = MyCat $ \(e, x) -> case e of
        Left y  -> Left (y, x)
        Right z -> Right (z, x)

instance (HasRep a, r ~ Rep a) => RepCat MyCat a r where
    reprC = MyCat repr
    abstC = MyCat abst

instance (Enum a, Show a) => EnumCat MyCat a where
    succC = MyCat succ
    predC = MyCat pred

instance BoolCat MyCat where
    notC = MyCat not
    andC = MyCat (uncurry (&&))
    orC  = MyCat (uncurry (||))
    xorC = MyCat (uncurry (/=))

instance IfCat MyCat a where
    ifC = MyCat (\(b, (t, e)) -> if b then t else e)

instance Num a => NumCat MyCat a where
    negateC = MyCat negate
    addC    = MyCat (uncurry (+))
    subC    = MyCat (uncurry (-))
    mulC    = MyCat (uncurry (*))
    powIC   = MyCat (uncurry (^))
