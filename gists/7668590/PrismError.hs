{-# LANGUAGE TemplateHaskell #-}

import Control.Lens

data Expr = Accessor  {_name :: String }
          | NOP

makeLenses (''Expr)
makePrisms (''Expr)

test :: Prism' Expr String
test = _Accessor

main = do
	print "hello"
