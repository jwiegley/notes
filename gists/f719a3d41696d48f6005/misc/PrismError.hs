{-# LANGUAGE TemplateHaskell #-}

import Control.Applicative
import Control.Lens

data Expr = Accessor  {_name :: String, _foo :: Int }
          | NOP
          deriving Show

makeLenses (''Expr)

test :: Traversal' Expr String
test = name

main = print $ Main.Accessor "John" 41 ^. test
