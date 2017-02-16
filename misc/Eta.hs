{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Eta where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Functor.Identity
import Data.Monoid

main =
    let m = undefined :: Identity (Either e a)
    in (join :: Identity (Identity (Either e a)) -> Identity (Either e a))
     ((return :: (Either e a -> Identity (Either e a))
                 -> Identity (Either e a -> Identity (Either e a)))
        ((\(xv :: Either e a) ->
         case xv of
         Left e -> (return :: Either e a -> Identity (Either e a)) (Left e)
         Right x' -> return (Right x')) :: Either e a -> Identity (Either e a))
        <*> (m :: Identity (Either e a)))
