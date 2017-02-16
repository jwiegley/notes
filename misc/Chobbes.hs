module Main where

import Data.Attoparsec.Text
import qualified Data.Text as T
import Control.Applicative
import Control.Monad.State
import Control.Monad.Trans.Except
import Debug.Trace

type EvalParser = StateT Integer (ExceptT String Parser)

liftP :: Parser a -> EvalParser a
liftP = lift . lift

parseOp :: Char -> Parser ()
parseOp c = do skipSpace
               char c
               skipSpace

parseAssign :: EvalParser Double
parseAssign = do val <- addExpr
                 modify (+1)
                 return val

addExpr :: EvalParser Double
addExpr = do val <- trace "addExpr: factor" $ factor
             rest <- trace "addExpr: addExpr'" $ addExpr'
             return $ val + rest
             
addExpr' :: EvalParser Double
addExpr' = trace "terms" terms <|> trace "return 0" (return 0)
  where terms :: EvalParser Double
        terms = do liftP $ trace "parseOp" $ parseOp '+'
                   l <- trace "factor" factor
                   r <- trace "addExpr'" addExpr'
                   return $ trace "+" $ l + r

factor :: EvalParser Double
factor = liftP double

parseEval :: EvalParser a -> String -> Either String (Either String (a, Integer))
parseEval p str = parseOnly (runExceptT (runStateT p 0)) (T.pack str)

main :: IO ()
main = do print $ parseEval addExpr "1 + 2"
