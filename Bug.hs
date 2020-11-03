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

{-@ data IntPair a = IntPair {
      pFirst :: Int,
      pSecond :: _
    } @-}
data IntPair a = IntPair
  { pFirst :: Int,
    pSecond :: a
  }
  deriving (Eq)

{-@ nubFst ::
      forall <p :: IntPair a -> Bool>.
      xs:[(IntPair a)<p>] ->
      {ys:[(IntPair a)<p>]<{\x y -> pFirst x /= pFirst y}> | len ys <= len xs}
      / [len xs] @-}

nubFst :: [IntPair a] -> [IntPair a]
nubFst [] = []
nubFst (x : xs) = x : nubFst (Bug.filter (\y -> pFirst x /= pFirst y) xs)
