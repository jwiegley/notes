{-# LANGUAGE OverloadedStrings #-}

module Sexp where

import Data.Text
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Text

data Sexp = Atom Text
          | Sub [Sexp]
          deriving Show

data Sexp = Sexp Text deriving Show

sexp :: Parser Sexp
sexp = undefined

ast :: Parsec Sexp () AST
ast = undefined

main = parseTest sexp "(foo)"
