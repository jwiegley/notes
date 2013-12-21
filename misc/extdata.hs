{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.Trans.State
import Data.Extensible.Product
import Data.Typeable

data Xyzzy = Xyzzy deriving Typeable

data Globals = Globals

instance ExtProdC Globals Xyzzy where
    type ExtProdF Xyzzy = String
    defaultExtProd _ _ = ""

foo :: StateT (ExtProd Globals) IO ()
foo = do
    st <- get
    let xyzzy = getExtProd st Xyzzy
    liftIO $ print xyzzy

main = flip runStateT globals foo
  where
    globals = constructExtProd Globals
                  [ Xyzzy :*= "Hello"
                  ]
