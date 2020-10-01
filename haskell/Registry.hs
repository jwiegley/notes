module Registry where

import Control.Arrow
import Data.ByteString
import Data.List (sortOn)
import Data.Map as Map
import Data.Maybe (fromMaybe)

type Version = Int -- we say Int, but we mean natural numbers

-- A registry is conceptually a mapping of keys to possible values at a given
-- Version. The meaning of keys and values themselves is opaque to us, so they
-- are represented as abstract types.
type Registry k v = Version -> k -> Maybe v

-- An update maps a set of keys to either known values or Nothing.
newtype Update k v = Update (Map k (Maybe v))

-- An update is a semigroup with the meaning of a right-biased union.
instance Ord k => Semigroup (Update k v) where
  Update l <> Update r = Update (r `union` l)

-- An update as also a monoid because we can define the "no-op update".
instance Ord k => Monoid (Update k v) where
  mempty = Update mempty
  mappend = (<>)

-- An update at a given version is effectively a value mask beyond that
-- version.
update :: Ord k => Registry k v -> Version -> Update k v -> Registry k v
update reg ver (Update m) = \v key ->
  if ver <= v
    then fromMaybe (reg v key) (Map.lookup key m)
    else reg v key

-- If we use a representation where the set of extant keys is enumerable at
-- any given version, then we can recover the set of changes made to a
-- registry between versions by inferring what the updates must have been.
changes ::
  (Ord k, Bounded k, Enum k) =>
  Registry k v ->
  Version ->
  Version ->
  [Update k v]
changes reg old new = Prelude.map inferUpdate [old .. new]
  where
    inferUpdate ver =
      Update $
        Map.fromList $ Prelude.map (id &&& reg ver) [minBound .. maxBound]

-- So what is a decent representation of an Internet Computer Registry? We
-- could go with a typical database over ByteStrings, where we track the
-- values at various versions.

type ActualRegistry = Map ByteString [(Version, Maybe ByteString)]

-- Now we prove that this maps into our model. It doesn't have to be a
-- bijection, but it must be an injection. This functions also does not need
-- to be efficient, since the above is only about establishing meaning, not
-- actual operation.

isRegistry :: ActualRegistry -> Registry ByteString ByteString
isRegistry reg = \ver key ->
  case Map.lookup key reg of
    Nothing -> Nothing
    Just xs -> case Prelude.filter ((> ver) . fst) (sortOn fst xs) of
      [] -> Nothing
      (_, x) : _ -> x

-- We only need to record past version if we want users to be able to query
-- them. Otherwise, if we only keep the "most recent" meaning at each key, we
-- can simplify further.
