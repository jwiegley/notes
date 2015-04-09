{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FunctionalDependencies #-}

module Container where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.State
import Data.Maybe
import Data.Monoid

data Container (p :: k -> *) (a :: *) where
    -- Need pi-types for this!
    Box :: forall p (x :: k) a. x -> (p x -> a) -> Container p a

type family S k :: * where
    S () = Float

main :: IO ()
main = do
    let action = do
            x <- get
            return $ floor x + 10
    case Box (evalState action) :: Container S Int of
        Box b -> print (b (10.0 :: Float))
