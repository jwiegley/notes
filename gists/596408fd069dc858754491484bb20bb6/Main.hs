module Main where

import Control.Monad.Free.VanLaarhovenE

type CacheKey = String

data Cache v effects m = Cache
               { _fetchCache :: CacheKey -> Free effects v -> m v
               }

fetchCache :: HasEffect effects (Cache v effects) => CacheKey -> Free effects v -> Free effects v
fetchCache key operation = liftVL (\c -> _fetchCache c key operation)

liftVL :: HasEffect effects effect => (forall m. effect m -> m a) -> Free effects a
liftVL getOp = Free (getOp . getEffect)
