{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Darais where

import Debug.Trace

newtype Fix f = Fix { unFix :: f (Fix f) }

data ExprF r = Val Int | Add r r
    deriving (Functor, Foldable, Traversable)

type Expr = Fix ExprF

cata' :: Monoid b
      => (ExprF a -> a)
      -> ((Expr -> (b, Maybe a)) -> (Expr -> (b, Maybe a)))
      -> (Expr -> (b, Maybe a))
cata' f g = g (fmap (fmap f . sequenceA) . traverse (cata' f g) . unFix)

eval :: Expr -> ((), Maybe Int)
eval = cata' phi psi
  where
    phi (Val x) = x
    phi (Add x y) = x + y

    psi k v@(Fix (Val _))   = trace "Evaluating Val" $ k v
    psi k v@(Fix (Add _ _)) = trace "Evaluating Add" $ k v
