{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}

module Broma where

import Data.Attoparsec.ByteString.Char8
import Data.ByteString.Char8
import Control.Monad.Free
import Control.Applicative

--
-- Query ---------------------------------------------------

type Query = Free Stmt
type Key   = ByteString
type Val   = ByteString

data Stmt k
    = Get Key (Val -> k)
    | Put Key Val k
    | Del Key k
    deriving (Functor)

get :: Key -> Query Val
get k = liftF (Get k id)

put :: Key -> Val -> Query ()
put k v = liftF (Put k v ())

del :: Key -> Query ()
del k = liftF (Del k ())

--
-- Parser --------------------------------------------------

-- | Parse any query
pQuery :: Parser (Query k)      -- This doesn't type check due to the type
pQuery = pGet <|> pPut <|> pDel -- mismatch between put/del and get.

-- | Parse a Get query
pGet :: Parser (Query Val)
pGet = string "get" *> (parens p)
  where p = stringLit >>= pure . get . pack

-- | Parse a Put query
pPut :: Parser (Query ())
pPut = string "put" *> (parens p)
  where p = do k <- stringLit
               char ','
               v <- stringLit
               pure (put (pack k) (pack v))

-- | Parse a Del query
pDel :: Parser (Query ())
pDel = string "del" *> (parens p)
  where p = stringLit >>= pure . del . pack

-- | Helpers
stringLit = char '\'' *> many (notChar '\'') <* char '\''
parens p = char '(' *> p <* char ')'
