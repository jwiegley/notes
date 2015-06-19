module Azor where

import Data.List

azorAhai :: (a -> a -> [a] -> [a]) -> [a] -> [a]
azorAhai f elements =
    foldl' xs elements [0..length elements]
  where
    xs elems i = foldl' ys elems [0..length elements]
      where
        ys elems' = go elems' i

    go elems i j = do
        let e1 = elems !! i
        let e2 = elems !! j
        f e1 e2 elems
