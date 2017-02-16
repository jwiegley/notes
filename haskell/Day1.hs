{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Day1 where

data Expr :: * where
  Lit   :: Int -> Expr
  True  :: Expr
  False :: Expr
  Less  :: Expr -> Expr -> Expr
  Plus  :: Expr -> Expr -> Expr
  If    :: Expr -> Expr -> Expr -> Expr
