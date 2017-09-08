{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}

module Darais where

import Debug.Trace

newtype Fix f = Fix { unFix :: f (Fix f) }

data ExprF a r = Val a | Add r r
    deriving Functor

type Expr a = Fix (ExprF a)

cataDer :: (ExprF i a -> a)
        -> (forall r. ExprF i (Expr i) -> (ExprF i (Expr i) -> r) -> r)
        -> Expr i
        -> a
cataDer f k (Fix x) = k x (f . fmap (cataDer f k))

eval :: Expr Int -> Int
eval = cataDer phi psi
  where
    phi (Val x) = x
    phi (Add x y) = x + y

    psi :: forall r i. ExprF i (Expr i) -> (ExprF i (Expr i) -> r) -> r
    psi v@(Val _)   k = trace "Evaluating Val" $ k v
    psi v@(Add _ _) k = trace "Evaluating Add" $ k v
