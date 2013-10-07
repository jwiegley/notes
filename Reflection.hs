{-# LANGUAGE FlexibleContexts #-}

module Reflection where

import Data.Proxy
import Data.Reflection

foo :: Reifies s Int => Proxy s -> IO Int
foo p = return $ reflect p

main :: IO ()
main = reify 10 $ \p -> do
    x <- foo p
    print x
