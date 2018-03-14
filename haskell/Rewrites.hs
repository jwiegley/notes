module Problem where

import Data.Tuple (swap)
import Control.Monad (guard)

zippers :: Eq a => [a] -> [a] -> [([a], [a])]
zippers xs = go []
  where
    go _ [] = []
    go b l@(y:ys) =
        let (pre, post) = splitAt (length xs) l
            next = go (y:b) ys in
        if pre == xs
        then (reverse b, post) : next
        else next

-- | Given a list of pairs of lists, where each pair (XS, YS) indicates that
--   XS may be substituted for YS in the left-hand side of the goal, is there
--   a sequence of subsitutions that will transform the LHS into the RHS? The
--   return value is a list of indices of rewrites applied.
--
--   For every substitution allowed, we only consider the reverse direction.
--
-- >>> findSubstitutions [([2,3],[5,3,5]),
--                        ([5,3],[9]),
--                        ([5,3],[3,5])]
--                        ([1,2,3,4,5],[1,9,5,4,5])
-- Just [0,2]
findSubstitutions :: Eq a => [([a], [a])] -> ([a],[a]) -> Maybe [Int]
findSubstitutions hyps (have, want) =
    case go [] [] have of
        []  -> Nothing
        r:_ -> Just (reverse r)
  where
    go tried path lhs
        | lhs == want = return path
        | otherwise = do
              (i, (l, r)) <- zip [0 :: Int ..] (hyps ++ map swap hyps)
              (pre, post) <- zippers l lhs
              let cand = pre ++ r ++ post
              guard (cand `notElem` tried)
              go (cand:tried) (i:path) cand
