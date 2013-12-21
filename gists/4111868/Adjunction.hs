{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Adjunction where

import Prelude (Num)

undefined ∷ a
undefined = undefined

($) ∷ (a → b) → a → b
f $ x = f x

flip ∷ (a → b → c) → b -> a → c
flip f x y = f y x

const ∷ a → b → a
const x _ = x

fst ∷ (a,b) → a
fst (x,_) = x

snd ∷ (a,b) → b
snd (_,x) = x

class Category cat where
  id  ∷ cat a a
  (∘) ∷ cat b c → cat a b → cat a c

instance Category (→) where
  id f = f
  (f ∘ g) x = f (g x)

class Functor f where
  fmap ∷ (a → b) → f a → f b

class (Functor f, Functor g) ⇒ Adjunction f g where
  η ∷ a → g (f a)               -- unit (natural transformation)
  ε ∷ f (g a) → a               -- counit (natural transformation)
  φ ∷ (f a → b) → a → g b       -- two natural isomorphisms
  ψ ∷ (b → g a) → f b → a

  η   = φ id
  ε   = ψ id
  φ f = fmap f ∘ η
  ψ g = ε ∘ fmap g

class Adjunction f g ⇒ Monad f g where
  μ ∷ g (f (g (f a))) → g (f a)
  μ = fmap ε

  (>>=) ∷ g (f a) → (a → g (f b)) → g (f b)
  x >>= f = μ (fmap (fmap f) x)

  (>>) ∷ g (f a) → g (f b) → g (f b)
  x >> f = x >>= \_ → f

class Adjunction f g ⇒ Comonad f g where
  δ ∷ f (g a) → f (g (f (g a)))
  δ = fmap η

  (=>>) ∷ f (g a) → (f (g a) → b) → f (g b)
  x =>> f = fmap (fmap f) (δ x)

class (Category cat, Adjunction f g) ⇒ Kleisli cat f g where
  idT ∷ cat a (g (f a))
  (<=<) ∷ cat b (g (f c)) → cat a (g (f b)) → cat a (g (f c))

instance Monad f g ⇒ Kleisli (→) f g where
  idT     = η
  g <=< f = μ ∘ fmap (fmap g) ∘ f

type Prod d = (,) d

instance Functor (Prod d) where
  fmap f (x,y) = (x, f y)

type Hom e = (→) e

instance Functor (Hom e) where
  fmap = (∘)

instance d ~ e ⇒ Adjunction (Prod d) (Hom e) where
  -- η ∷ a → g (f a)
  -- η ∷ a → (e → f a)
  -- η ∷ a → e → f a
  -- η ∷ a → e → (e,a)
  η x y = (y,x)

  -- ε ∷ f (g a) → a
  -- ε ∷ f (e → a) → a
  -- ε ∷ (e, e → a) → a
  -- ε ∷ (e, e → a) → a
  ε (y,f) = f y

  -- φ ∷ (f a → b) → a → g b
  -- φ ∷ (f a → b) → a → e → b
  -- φ ∷ ((e,a) → b) → a → e → b
  -- φ f     = fmap f ∘ η
  -- φ f x y = (fmap f ∘ η) x y
  -- φ f x y = (fmap f ∘ \x y → (y,x)) x y
  -- φ f x y = (fmap f ∘ \x → \y → (y,x)) x y
  -- φ f x y = (fmap f (\y → (y,x))) y
  -- φ f x y = (f ∘ (\y → (y,x))) y
  φ f x y = f (y,x)

  -- ψ ∷ (b → g a) → f b → a
  -- ψ ∷ (b → e → a) → f b → a
  -- ψ ∷ (b → e → a) → (e,b) → a
  -- ψ g       = ε ∘ fmap g
  -- ψ g (y,f) = (ε ∘ fmap g) (y,f)
  -- ψ g (y,f) = ε (fmap g (y,f))
  -- ψ g (y,f) = ε (y,g f)
  -- ψ g (y,f) = (g f) y
  ψ g (y,f) = g f y

instance d ~ e ⇒ Monad   (Prod d) (Hom e)
instance d ~ e ⇒ Comonad (Prod d) (Hom e)

type State s a = Hom s (Prod s a)

get ∷ State s s
get s = (s,s)

put ∷ s → State s ()
put s _ = (s,())

runState ∷ State s a → s → (s,a)
runState act = act

evalState ∷ State s a → s → a
evalState = (snd ∘) ∘ runState

execState ∷ State s a → s → s
execState = (fst ∘) ∘ runState

foo ∷ Num a ⇒ State a a
foo = runState $ put 10 >> get

class Monoid m where
  mempty  ∷ m
  mappend ∷ m → m → m

instance Monoid (a → a) where
  mempty  = id
  mappend = (∘)

instance Monad f g ⇒ Monoid (a → g (f a)) where
  mempty  = idT
  mappend = (<=<)

-- Adjunction.hs ends here
