module RangeLens where

import Control.Applicative
import Control.Lens
import Control.Lens.Indexed as Lens
import Data.Maybe (fromMaybe)

class Functor f => IxRangeable f m where
    ixrel :: Index m -> IndexedLensLike' (Index m) f m (IxValue m)
    ixrange :: Maybe (Index m) -> Maybe (Index m)
            -> IndexedLensLike' [Index m] f m [IxValue m]

type instance IxValue [a] = a
instance Applicative f => IxRangeable f [a] where
    ixrel i f xs
        | i < 0 = ixrel (i + len) f xs
        | otherwise = go xs i
      where
        go [] _ = pure []
        go (a:as) 0 = Lens.indexed f i a <&> (:as)
        go (a:as) j = (a:) <$> (go as $! j - 1)
        len = length xs

    ixrange mlb mub f xs
        | lb < 0 = ixrange (Just (lb + len)) (Just ub) f xs
        | ub < 0 = ixrange (Just lb) (Just (ub + len)) f xs
        | lb < ub && ub <= len =
            let (beg, rest) = splitAt lb xs
                (mid, end)  = splitAt (ub - lb) rest
            in (++) <$> ((++) <$> pure beg
                              <*> Lens.indexed f [lb..pred ub] mid)
                    <*> pure end
        | otherwise = pure xs
      where
        lb = fromMaybe 0 mlb
        ub = fromMaybe len mub
        len = length xs

-- | Splice a range of a list using a lens, supporting Python-style indices.
--
-- >>> [1,2,3,4,5] ^. irange 1 (-2)
-- [2,3]
-- >>> [1,2,3,4,5] ^. irange 3 (-1)
-- [4]
-- >>> [1,2,3,4,5] ^. irange (-2) 4
-- [4]
irange :: IxRangeable f m
       => Index m -> Index m -> IndexedLensLike' [Index m] f m [IxValue m]
irange lb ub = ixrange (Just lb) (Just ub)

-- | Performs the same action as 'irange', only it assumes an upper bound
--   equal to the length of the list.
ifrom :: IxRangeable f m
      => Index m -> IndexedLensLike' [Index m] f m [IxValue m]
ifrom lb = ixrange (Just lb) Nothing

-- | Performs the same action as 'irange', only it assumes a lower bound set
--   at the beginning of the list.
iuntil :: (IxRangeable f m, Num (Index m))
       => Index m -> IndexedLensLike' [Index m] f m [IxValue m]
iuntil = ixrange Nothing . Just
