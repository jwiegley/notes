module LensConduit where

import Control.Lens
import Data.Conduit
import Data.Conduit.List as CL
import Data.Monoid
import Data.Foldable

narrow :: Monad m => Getting (First a) i a -> ConduitM i a m ()
narrow l = awaitForever $ traverse_ yield . preview l

main :: IO ()
main = do
    sourceList [Left 10, Right 20, Left 30]
        $= narrow _Left
        $$ CL.mapM_ print

    sourceList [(10, Left 'a'), (20, Right 'b'), (30, Left 'c')]
        $= narrow (_2 . _Left . filtered (== 'a'))
        $$ CL.mapM_ print
