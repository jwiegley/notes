{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}

import Control.Monad

getRandoms' :: (Monad m) => (forall a. (Num a) => m a) -> m (Int, Double)
getRandoms' getRandom = liftM2 (,) getRandom getRandom

getRandoms :: (Monad m, Num a) => m a -> m (Int, Double)
getRandoms getRandom = liftM2 (,) getRandom getRandom

