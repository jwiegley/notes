{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeApplications #-}

module Darais where

import Control.Monad
import Data.Functor.Identity
import Debug.Trace

newtype Fix f = Fix { unFix :: f (Fix f) }

data ExprF r = Val Int | Add r r
    deriving (Functor, Foldable, Traversable)

type Expr = Fix ExprF

adi :: (Monoid b, Applicative s, Traversable t)
    => (t a -> a)
    -> ((Fix t -> (b, s a)) -> Fix t -> (b, s a))
    -> Fix t -> (b, s a)
adi f g = g (go . traverse (adi f g) . unFix)
  where
    go = fmap (fmap f . sequenceA)

adiM :: (Monoid b, Applicative s, Traversable s, Traversable t, Monad m)
     => (t a -> m a)
     -> ((Fix t -> m (b, s a)) -> Fix t -> m (b, s a))
     -> Fix t -> m (b, s a)
adiM f g = g ((go <=< traverse (adiM f g)) . unFix)
  where
    go = traverse (traverse f . sequenceA) . sequenceA

-- A type application is needed below because we do not generate any value
-- from the analysis; it does tracing only.

denote :: ExprF Int -> Int
denote (Val x)   = x
denote (Add x y) = x + y

eval :: Expr -> Int
eval = runIdentity . snd . adi @() denote psi
  where
    psi k v@(Fix (Val _))   = trace "Evaluating Val" $ k v
    psi k v@(Fix (Add _ _)) = trace "Evaluating Add" $ k v

evalM :: Expr -> IO Int
evalM = fmap (runIdentity . snd) . adiM @() (pure <$> denote) psi
  where
    psi k v@(Fix (Val _))   = putStrLn "Evaluating Val" >> k v
    psi k v@(Fix (Add _ _)) = putStrLn "Evaluating Add" >> k v
