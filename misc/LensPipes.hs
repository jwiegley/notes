module LensPipes where

import           Control.Applicative
import           Control.Lens
import           Control.Lens.Internal.Bazaar
import           Control.Monad
import           Pipes
import           Pipes.Core
import           Pipes.Lift
import qualified Pipes.Prelude as P

pipe :: Monad m => Lens' Int (Producer Int m ())
pipe k n = n <$ k (do
    yield $ n + 1
    yield $ n + 2
    yield $ n + 3
    yield $ n + 4)

within :: Monad m => Traversing (->) m (Producer a m r) (Producer b m r) a b
within k p = BazaarT $ \x -> p >-> P.mapM (flip runBazaarT x . k)

main :: IO ()
main = do
    runEffect $ for (100 ^. pipe.to (+3)) (liftIO . print)
