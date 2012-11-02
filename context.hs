{-# LANGUAGE PolymorphicComponents, RankNTypes, TypeFamilies #-}

module Traversal where

import Control.Applicative
import Control.Arrow
import Control.Comonad
import Control.Comonad.Identity
import Data.Functor
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
  runContextF :: forall f. Functor f => (b -> f t) -> f a
}

instance a ~ b => Functor (ContextF a b) where
  fmap f (ContextF g) = ContextF (fmap f . g)

instance a ~ b => Comonad (ContextF a b) where
  extract (ContextF f)   = runIdentity (f Identity)
  duplicate (ContextF g) = getCompose (g (Compose . fmap ctxt . ctxt))
  extend f w             = fmap f (duplicate w)

ctxt :: a -> ContextF a b t
ctxt i = ContextF (\k -> k i)

getF :: ContextF a b t -> a
getF (ContextF g) = getConst (g Const)

modifyF :: (a -> a) -> ContextF a a t -> a
modifyF f w@(ContextF g) = g (f w)

experimentF :: [a -> a] -> ContextF a a t -> [a]
experimentF fs w = map (`modifyF` w) fs

liftCtxF :: (t -> a) -> ContextF a a t -> a
liftCtxF f (ContextF g) = undefined     -- jww (2012-11-01): TODO

-- context.hs ends here