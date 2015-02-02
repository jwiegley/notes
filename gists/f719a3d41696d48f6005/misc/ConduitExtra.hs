module ConduitExtra where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Conduit (($$))
import Data.Conduit.List as CL
import Data.Conduit.Extra.Pipes
import Data.Void

forC :: Monad m => Producer m a -> (a -> Producer m b) -> Producer m b
forC p f = p =$= loop
  where
    loop = do
        mx <- await
        case mx of
            Nothing -> return ()
            Just x -> do
                f x $$ CL.mapM_ yield
                loop

main :: IO ()
main = do
    runEffect $ forP p yield
    runEffect $ forP p (+1)
    runEffect $ forP (forP p (+1)) (+2)
    runEffect $ forP p (\x -> forP ((+1) x) (+2))
  where
    p = yield (10 :: Int)
