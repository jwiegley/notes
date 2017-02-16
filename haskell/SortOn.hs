import Data.List
import Data.Ord

-- | Sort a list by comparing the results of a key function applied to each
--   element.  @sortOn f@ is equivalent to @sortBy . comparing f@, but has the
--   performance advantage of only evaluating @f@ once for each element in the
--   input list.  This is called the decorate-sort-undecorate paradigm, or
--   Schwartzian transform.
sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn f = map snd . sortBy (comparing fst)
                   . map (\x -> let y = f x in y `seq` (y, x))

main = print $ sortOn length [[1], [1, 2, 3], [1, 2]]
