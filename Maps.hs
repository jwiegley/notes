{-# LANGUAGE OverloadedStrings #-}

module Maps where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Map
import Data.Maybe
import Data.Monoid
import Data.Proxy
import Data.Tagged

data Wrapped = Wrapped { unwrap :: forall r. (r -> r) -> r }

foo :: Map String Wrapped -> String -> (r -> r) -> Maybe r
foo xs k f = flip unwrap f <$> Data.Map.lookup k xs

main :: IO ()
main = do
    print (foo (Data.Map.fromList
                    [ ("hello", Wrapped (\f -> f (10 :: Int))) ])
               "hello"
               (+1) :: Maybe Int)
