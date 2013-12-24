module LensConduit where

import Control.Lens
import Data.Conduit
import Data.Conduit.List as CL
import Data.Monoid

narrow :: Monad m => Getting (First a) i a -> ConduitM i a m ()
narrow l = awaitForever $ maybe (return ()) yield . preview l

main :: IO ()
main = sourceList [Left 10, Right 20, Left 30]
    $= narrow _Left
    $$ CL.mapM_ print
