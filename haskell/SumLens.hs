{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Sum.Lens where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Constraint

projected :: e :< r => Prism' (Sum r v) (e v)
projected = prism' inject project

projectedC :: forall r v e. Const e :< r => Prism' (Sum r v) e
projectedC = prism' (inject . Const) (fmap getConst . project)

weakened :: Prism' (Sum (e ': r) v) (Sum r v)
weakened = prism' weaken $ \s -> case decompose s of
  Left es -> Just es
  Right _ -> Nothing

_shead :: Prism' (Sum (e ': r) v) (e v)
_shead = projected

_stail :: Prism' (Sum (e ': r) v) (Sum r v)
_stail = weakened

underneath :: e :< r => Prism' (Sum (s ': r) v) (e v)
underneath = weakened . projected

underneathC :: forall r v s e. Const e :< r => Prism' (Sum (s ': r) v) e
underneathC = weakened . projectedC

decomposed :: Iso' (Sum (e ': r) v) (Either (Sum r v) (e v))
decomposed = iso decompose (either weaken inject)

-- | @applied@ is the optic version of apply, to make it easy to compose
--   applications with other optics:
--   @@
--   s ^. applied @Printable printItem
--     === apply @Printable printItem s
--   @@
applied ::
  forall c r v a.
  Apply c r =>
  (forall f. c f => f v -> a) ->
  Fold (Sum r v) a
applied k f s = s <$ f (apply @c k s)

-- | @HasTraversal'@ serves the same role as Apply, but for traversals across
--   sums that support a given optic. For example, and with direct analogy to
--   'Apply':
--   @@
--   class HasLot f where
--     _Lot :: Traversal' (f v) Lot
--
--   instance HasTraversal' HasLot fs => HasLot (Sum fs) where
--     _Lot = traversing @HasLot _Lot
--   @@
class HasTraversal' (c :: (* -> *) -> Constraint) (fs :: [* -> *]) where
  traversing :: (forall g. c g => Traversal' (g a) b) -> Traversal' (Sum fs a) b

instance c t => HasTraversal' c '[t] where
  traversing k f s = fmap inject (k f (decomposeLast s))

instance
  {-# OVERLAPPING #-}
  (HasTraversal' c (u ': r), c t) =>
  HasTraversal' c (t ': u ': r)
  where
  traversing k f s = case decompose s of
    Right e -> inject <$> k f e
    Left es -> weaken <$> traversing @c k f es

class HasFold (c :: (* -> *) -> Constraint) (fs :: [* -> *]) where
  plied :: (forall g. c g => Fold (g a) b) -> Fold (Sum fs a) b

instance c t => HasFold c '[t] where
  plied k f s = fmap inject (k f (decomposeLast s))

instance
  {-# OVERLAPPING #-}
  (HasFold c (u ': r), c t) =>
  HasFold c (t ': u ': r)
  where
  plied k f s = case decompose s of
    Right e -> inject <$> k f e
    Left es -> weaken <$> plied @c k f es

{-
-- instance (Apply Eq1 r, Eq e) => Apply Eq1 (Const e : r) where
--   apply f s = case decompose s of
--     Left es -> apply @Eq1 f es
--     Right r -> f r

works :: (Apply Eq1 r, Eq v) => Sum r v -> Sum r v -> Bool
works x y = x == y

-- Could not deduce (Apply Eq1 (Const () : r))
-- fails :: (Apply Eq1 r, Eq v) => Sum r v -> Sum r v -> Bool
-- fails x y = weaken @_ @_ @(Const ()) x == weaken y

stronger :: f :< r => Sum r v -> a
stronger = undefined

-- debilitate ::
--   forall t f a.
--   t :< f =>
--   Proxy (ElemIndex t f) ->
--   (forall t f any. t :< (any ': f) => Proxy (ElemIndex t (any ': f)) -> a) ->
--   a
-- debilitate p f =
--   unsafeCoerce (MagicSucc f :: MagicSucc a) (trickValue (natVal p)) Proxy

weaker :: Const Int :< r => Sum (Const Double ': r) v -> f v
weaker = stronger @(Const Int) -- debilitate (Proxy :: Proxy (ElemIndex f r)) (const stronger)

-- newtype MagicSucc r
--   = MagicSucc
--       ( forall t f a.
--         t :< (a ': f) =>
--         Proxy (ElemIndex t f) ->
--         r
--       )

-- trickValue :: Natural -> Natural
-- trickValue = (+ 1)

-- weaker :: t :< r => (Sum r v -> a) -> Sum (e ': r) v -> Maybe a
-- weaker f = either (Just . f) (const Nothing) . decompose
-}

class Producible m f where
  produce :: m (f v)

class Populate m (fs :: [* -> *]) where
  populate :: m (Sum fs b)

instance (Producible m t, MonadPlus m) => Populate m '[t] where
  populate = fmap inject (produce @m @t)

instance
  {-# OVERLAPPING #-}
  (Populate m (u ': r), Producible m t, MonadPlus m) =>
  Populate m (t ': u ': r)
  where
  populate =
    fmap inject (produce @m @t)
      <|> fmap weaken (populate @m @(u ': r))
