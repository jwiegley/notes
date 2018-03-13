{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Lambda where

import Control.Applicative
import Control.Lens
import Control.Lens.Plated

data Type
    = Unit
    | Func
  deriving Show

data Expr where
  Var :: Int -> Expr
  Abs :: Type -> Expr -> Expr
  App :: Expr -> Expr -> Expr
  deriving Show

instance Plated Expr where
  plate f (Abs t x) = Abs t <$> f x
  plate f (App x y) = App <$> f x <*> f y
  plate _ v = pure v

calls :: Int -> Traversal' Expr Expr
calls n f (App (Var n') y) | n == n' = App (Var n') <$> f y
calls _ _ v = pure v

bar :: Expr
bar = App (Var 0) (App (Var 0) (Var 1))

baz :: Expr -> Expr
baz = rewriteOn (calls 0) go
  where
    go :: Expr -> Maybe Expr
    go (Var 0) = Just (Var 1)
    go _ = Nothing
