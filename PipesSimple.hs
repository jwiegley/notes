module PipesSimple where

import Control.Applicative
import Control.Monad.Trans.Either
import Data.Void

data Producer a m r
type Proxy a' a b' b m r =
    (a' -> EitherT r m a) ->
    (b  -> EitherT r m b') -> EitherT r m r

type Producer a m r = Proxy Void () () a m r

each :: [a] -> Producer a m ()
each xs = \await yield -> do
    yield (head xs)

toListM :: Producer a m () -> m [a]
toListM p = fmap (either id id) $ runEitherT $ p absurd (\b -> undefined)
