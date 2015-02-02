module Loeb where

import Control.Applicative
import Control.Monad
import Control.Comonad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Either
import Control.Monad.Trans.Control
import Data.List.NonEmpty as NE
import Data.Function
import Data.Functor.Identity
import Data.Maybe
import Data.Monoid

loeb :: Functor f => f (f a -> a) -> f a
loeb xs = ys where ys = fmap ($ ys) xs

floeb :: (e -> (e -> a) -> a) -> e -> a
floeb f x = f x g where g y = f y g

w_loeb :: Comonad w => w (w a -> a) -> w a
w_loeb w = fix (flip extend w . flip extract)

main :: IO ()
main = do
    print $ Prelude.take 10 $
       runIdentity $ loeb (Identity ((1 :) . runIdentity))
    print $ floeb (\e f -> if e < 10 then f (e + 1) else e) 1
    print $ fix (\f e -> if e < 10 then f (e + 1) else e) 1
    print $ w_loeb (   (\xs -> NE.length xs)
                    :| [ (\xs -> xs NE.!! 0)
                       , (\xs -> xs NE.!! 1 + 3)
                       ]
                   )
