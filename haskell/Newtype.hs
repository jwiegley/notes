{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Newtype where

import Control.Lens
import "newtype" Control.Newtype
import Data.MonoTraversable

instance Newtype n (Element n) => MonoFunctor n where
    omap f (unpack -> x) = pack (f x)

instance Newtype n (Element n) => MonoFoldable n where
    ofoldMap   f   (unpack -> x) = f x
    ofoldr     f z (unpack -> x) = f x z
    ofoldr1Ex  _   (unpack -> x) = x
    ofoldl'    f z (unpack -> x) = f z x
    ofoldl1Ex' _   (unpack -> x) = x

instance Newtype n (Element n) => MonoTraversable n where
    otraverse f (unpack -> x) = pack <$> f x

newtyped :: Newtype n o => Iso' n o
newtyped = iso unpack pack

-- This could all be TH-generated
newtype Foo = Foo { getFoo :: Int }
type instance Element Foo = Int
instance Newtype Foo Int where
    unpack = getFoo
    pack = Foo

test1 :: Int -> Int
test1 i = unpack (pack i :: Foo)

test2 :: Foo -> Foo
test2 i = pack (unpack i)

test3 :: Foo -> Int
test3 i = i^.newtyped

test4 :: Int -> Foo
test4 i = i^.from newtyped

test5 :: Foo -> Foo
test5 = omap (+1)

test6 :: Foo -> Int
test6 = ofoldr (*) 0

test7 :: Foo -> [Foo]
test7 = otraverse (:[])
