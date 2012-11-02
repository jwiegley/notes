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

data Context c a = Context (c -> a) c

instance Functor (Context c) where
  fmap f (Context g x) = Context (f . g) x

instance Comonad (Context c) where
  extract (Context g x)   = g x
  duplicate (Context g x) = Context (Context g) x
  extend f w              = fmap f (duplicate w)

get :: Context c a -> c
get (Context _ x) = x

modify :: (c -> c) -> Context c a -> a
modify f (Context g x) = g (f x)

experiment :: [c -> c] -> Context c a -> [a]
experiment fs w = map (`modify` w) fs

liftCtx :: (a -> b) -> Context c a -> b
liftCtx f (Context g x) = f (g x)

-- Functor-oriented version given by Edward Kmett as the basis for Lens (it is
-- a "pre-applied lens", where Lens has the type (c -> f d) -> s -> f b)

newtype ContextF c d b = ContextF {
  runContextF :: forall f. Functor f => (c -> f d) -> f b
}

instance Functor (ContextF c d) where
  fmap f (ContextF g) = ContextF (fmap f . g)

instance c ~ d => Comonad (ContextF c d) where
  extract (ContextF f)   = runIdentity (f Identity)
  duplicate (ContextF g) = getCompose (g (Compose . fmap ctxt . ctxt))
  extend f w             = fmap f (duplicate w)

ctxt :: c -> ContextF c d d
ctxt i = ContextF (\k -> k i)

getF :: ContextF c d b -> c
getF (ContextF g) = getConst (g Const)

modifyF :: (c -> c) -> ContextF c d b -> b
modifyF f w@(ContextF g) = undefined    -- jww (2012-11-01): TODO

experimentF :: [c -> c] -> ContextF c d b -> [b]
experimentF fs w = map (`modifyF` w) fs

liftCtxF :: (d -