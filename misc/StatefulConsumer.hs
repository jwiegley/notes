module StatefulConsumer where

import Pipes
import Control.Monad.Trans.State as S

counter :: (Show a) => Consumer a (StateT Integer IO) ()
counter = do
    x <- await
    lift $ S.modify (+1)
    liftIO $ print $ show x
    counter

main :: IO ()
main = do
    x <- flip S.execStateT 0 $ runEffect $ each [1,2,3,4,5,6] >-> counter
    print x
