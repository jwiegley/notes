module Fault where

import Control.Category
import Control.Monad
import Data.List (sortOn)
import Data.Monoid
import Prelude hiding ((.), id)

-- newtype Set a = Set { getSet :: a -> Bool }

-- instance Functor Set where
--     fmap f (Set p) = Set $ \b -> exists a. f a == b && p a

-- type Faulty = Kleisli []
newtype Valued a b = Valued { runValued :: a -> [(b, Sum Int)] }

instance Category Valued where
    id = Valued (\x -> return (x, Sum 0))
    Valued f . Valued g = Valued $ \x -> do
        (y, v)  <- g x
        (z, v') <- f y
        pure (z, v <> v')

cohere :: Valued a b -> a -> b
cohere (Valued f) x =
    case reverse (sortOn snd (f x)) of
        (b,_):_ -> b
