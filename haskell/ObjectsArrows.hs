module ObjectsArrows where

import Data.List (nub)

-- Given a number of objects in a category, generate all the possible
-- compositions of arrows in that category. This is sufficient to define the
-- "arrows only" definition of the category, since the existence of "objects"
-- may be indicated by their identity morphisms, and the domain and codomain
-- of "arrows" by how they compose with those identities.

makeArrows :: Int -> [((Int, Int), Int)]
makeArrows = go
  where
    go 0 = []
    go n =
        let xs = go (pred n)
            a  = length xs
            ys = concat [ [ ((a, f), f), ((f, x), f) ]
                        | (((x, y), _), f) <- zip xs [succ a..]
                        , x == y ]
            zs = xs ++ ((a, a), a) : ys in
        zs ++ nub [ ((y, x), a)
              | (((i, j), y), ((k, l), x)) <- [ (x, y) | x <- zs, y <- zs ]
              , i /= j, k /= l, l == i, j /= k, x /= y ]

arrowCount :: Int -> Integer
arrowCount 0 = 0
arrowCount n = fromIntegral n^2 + arrowCount (pred n)
