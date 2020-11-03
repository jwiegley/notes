module Bug where

{-@
filter :: forall <p :: a -> Bool, w :: a -> Bool -> Bool>.
                 {y :: a, b::{v:Bool<w y>|v} |- {v:a|v == y} <: a<p>}
                 (x:a -> Bool<w x>) -> xs:[a] ->
                 {ys:[a<p>] | len ys <= len xs}
@-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x : xs)
  | f x = x : Bug.filter f xs
  | otherwise = Bug.filter f xs
filter _ [] = []

{-@ cmp_fst ::
      Eq a => x:(a, b) -> y:(a, b) -> {b:Bool|b <=> fst x == fst y} @-}
{-@ inline cmp_fst @-}

cmp_fst :: Eq a => (a, b) -> (a, b) -> Bool
cmp_fst (x, _) (y, _) = x == y

{-@ not_cmp_fst ::
      Eq a => x:(a, b) -> y:(a, b) -> {b:Bool|b <=> fst x /= fst y} @-}
{-@ inline not_cmp_fst @-}

not_cmp_fst :: Eq a => (a, b) -> (a, b) -> Bool
not_cmp_fst (x, _) (y, _) = x /= y

{-@
nubFst :: Eq a => xs:[(a, b)] ->
          [(a, b)]<{\x y -> not_cmp_fst x y}> / [len xs]
@-}

nubFst :: Eq a => [(a, b)] -> [(a, b)]
nubFst [] = []
nubFst (x : xs) = x : nubFst (Bug.filter (not_cmp_fst x) xs)
