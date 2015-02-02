import Data.List
import Control.Monad

unfoldM :: MonadPlus m => (b -> Maybe (m a, b)) -> b -> m a
unfoldM = (foldr mplus mzero .) . unfoldr
