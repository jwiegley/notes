{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module FunType where

import Test.QuickCheck.Function

type family FunT (dom :: [*]) where
    FunT '[] = ()
    FunT (x ': xs) = x -> FunT xs

data FunD dom cod where
    Nil :: cod -> FunD '[] cod
    Sing :: (dom -> cod) -> FunD '[dom] cod
    Mult :: (dom -> FunD doms cod) -> FunD (dom ': doms) cod

foo :: FunD dom cod -> FunT dom :-> cod
foo (Nil c) = function (const c)
foo (Sing f) = function (\x _ -> f x)
