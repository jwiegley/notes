import Control.Monad.Free.VanLaarhovenE

type CacheKey = String

data Cache v m = Cache
               { _fetchCache :: forall effect. CacheKey -> effect v -> m v
               }

fetchCache :: HasEffect effects (Cache v) => CacheKey -> Free effects v -> Free effects v
fetchCache key operation = liftVL (\c -> _fetchCache c key operation)

liftVL :: HasEffect effects effect => (forall m. effect m -> m a) -> Free effects a
liftVL getOp = Free (getOp . getEffect)
