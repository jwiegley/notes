{-# LANGUAGE PolymorphicComponents, RankNTypes, TypeFamilies #-}

module Traversal where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Identity
import Data.Functor.Compose

-- This is called:
--
-- Context, by Paul Hachmann:
--   http://www.cas.mcmaster.ca/~carette/CAS706/F2006/presentations/comonads.pdf
--
-- Store, by r6research:
--   http://r6research.livejournal.com/23705.html
--
-- Costate, by Michael Lauer:
--   http://mrlauer.wordpress.com/2010/12/18/rambling-thoughts-about-comonads/

data Context a b t = Context (b -> t) a

instance Functor (Context a b) where
  fmap f (Context g x) = Context (f . g) x

instance a ~ b => Comonad (Context a b) where
  extract (Context g x)   = g x
  duplicate (Context g x) = Context (Context g) x
  extend f w              = fmap f (duplicate w)

get :: Context a b t -> a
get (Context _ x) = x

modify :: (a -> a) -> Context a a t -> t
modify f (Context g x) = g (f x)

experiment :: [a -> a] -> Context a a t -> [t]
experiment fs w = map (`modify` w) fs

liftCtx :: (t -> a) -> Context a a t -> a
liftCtx f (Context g x) = f (g x)

-- Functor-oriented version given by Edward Kmett as the basis for Lens (it is
-- a "pre-applied lens", where Lens has the type (c -> f d) -> s -> f b)

newtype ContextF a b t = ContextF {
  runContextF :: forall f. Functor f => (a -> f b) -> f t
}

instance Functor (ContextF a b) where
  fmap f (ContextF g) = ContextF (fmap f . g)

instance a ~ b => Comonad (ContextF a b) where
  extract (ContextF f)   = runIdentity (f Identity)
  duplicate (ContextF g) = getCompose (g (Compose . fmap ctxt . ctxt))
  extend f w             = fmap f (duplicate w)

ctxt :: a -> ContextF a b b
ctxt i = ContextF (\k -> k i)

getF :: ContextF a b t -> a
getF (ContextF g) = getConst (g Const)

modifyF :: (a -> a) -> ContextF a a t -> t
modifyF f (ContextF g) = runIdentity (g (Identity . f))

experimentF :: [a -> a] -> ContextF a a t -> [t]
experimentF fs w = map (`modifyF` w) fs

liftCtxF :: (t -> a) -> ContextF a a t -> a
liftCtxF f (ContextF g) = f (runIdentity (g Identity))

ctxToCtxF :: Context a b t -> ContextF a b t
ctxToCtxF (Context c x) = ContextF (\k -> fmap c (k x))

ctxFToCtx :: ContextF a b t -> Context a b t
ctxFToCtx w@(ContextF g) =  Context (g (flip const)) (getF w)

main :: IO()
main = do
  let x = Context takeInts 3
  print $ modify (+1) x

  let y = ctxToCtxF x
  print $ modifyF (+1) y

  let z = ctxFToCtx y
  print $ modify (+1) z

  let w = ContextF (\k -> fmap takeInts (k 3))
  print $ modifyF (+1) w

  where
    takeInts n = take n [1..10] :: [Int]

-- context.hs ends here