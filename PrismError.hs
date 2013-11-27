{-# LANGUAGE TemplateHaskell #-}

import Control.Applicative
import Control.Lens

data Expr = Accessor  {_name :: String, _foo :: Int }
          | NOP

makeLenses (''Expr)

test :: Applicative f => (String -> f String) -> Expr -> f Expr
test = name

main = print $ Main.Accessor "John" 41 ^? test
