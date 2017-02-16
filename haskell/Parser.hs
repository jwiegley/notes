module Parser where

import Control.Monad
import Data.Monoid

data Token = TokInt Int | TokStr String

-- A parser is a function that takes an input string and returns a list of
-- values for each parse of that string
data Parser a = Parser { getTokens :: [String], getValue :: a }

instance Monad Parser where
  return = Parser []            -- or: return x = Parser [] x

  -- A bind over a Parser calls the "parse" function and applies our function
  -- to the resulting value, recursively
  p >>= f = let p' = parse p in Parser (getTokens p') (f (getValue p'))

-- First we need a way to start the parsing process.  We'll assume that the
-- our value is a Monoid, giving us a meaning for "null value", or mempty
setTokens :: (Monoid a) => [String] -> Parser a
setTokens = flip Parser mempty

-- And let's have a function to parse strings.  Note that it takes no
-- arguments!
parse :: Parser a -> Parser a
parse p = Parser (tail (getTokens p)) (TokStr (head (getTokens p)))

doParse :: Parser [Token]
doParse = do
  setTokens (words "Hello, world!")
  x <- parseStr
  y <- parseStr
  return [x, y]

main :: IO ()
main = do
  toks <- doParse
  putStrLn toks