-- Parsec 3 tutorial code --

-- module Main where -- this isn't necessary

import Text.Parsec
import Text.Parsec.String (Parser) -- type Parser = Parsec String ()
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellStyle)
import Data.Char
-- import Control.Monad.Identity -- for the Identity monad

simple :: Parser Char
simple = letter

run :: Show a => Parser a -> String -> IO ()
run p input =
    case (parse p "" input) of
        Left err -> do putStr "parse error at "
                       print err
        Right x  -> print x

openClose :: Parser Char
openClose = do char '('
               char ')'

{- -- parens is defined in Text.Parsec.Token
parens :: Parser ()
parens = do char '('
            parens
            char ')'
            parens
        <|> return ()
-}

testOr :: Parser String
testOr = string "(a)"
     <|> string "(b)"

testOr1 :: Parser Char
testOr1 = do char '('
             char 'a' <|> char 'b'
             char ')'

testOr2 :: Parser String
testOr2 = try (string "(a)") 
      <|> string "(b)"

testOr3 :: Parser String
testOr3 = do try (string "(a")
             char ')'
             return "(a)"
      <|> string "(b)"

nesting :: Parser Int
nesting = do char '('
             n <- nesting
             char ')'
             m <- nesting
             return (max (n+1) m)
         <|> return 0

{-
word :: Parser String
word = do{ c <- letter
         ; do{ cs <- word
             ; return (c:cs) 
             }
           <|> return [c]
         }
-}

{-
word :: Parser String
word = do c <- letter
          do cs <- word
             return (c:cs) 
           <|> return [c]       -- <|> indentation is confusing here, but it works
-}

--word :: Parser String
--word = many1 letter

{-
sentence :: Parser [String]
sentence = do words <- sepBy1 word separator
              oneOf ".?!"
              return words

separator :: Parser ()
separator = skipMany1 (space <|> char ',')
-}


word :: Parser String
word = many1 letter <?> "word"

separator :: Parser ()
separator = skipMany1 (space <|> char ',' <?> "")

sentence :: Parser [String]
sentence = do words <- sepBy1 word separator
              oneOf ".?!" <?> "end of sentence"
              return words

{- 
expr :: Parser Integer
expr = buildExpressionParser table factor <?> "expression"

table = [[op "*" (*) AssocLeft, op "/" div AssocLeft]
        ,[op "+" (+) AssocLeft, op "-" (-) AssocLeft]
        ]
        where op s f assoc 
                  = Infix (do{ string s; return f}) assoc

factor = do char '('
            x <- expr
            char ')'
            return x
        <|> number
        <?> "simple expression"
-}

number :: Parser Integer
number = do ds <- many1 digit
            return (read ds)
        <?> "number"
{-
lexer :: P.TokenParser ()
lexer = P.makeTokenParser (haskellStyle 
                           { P.reservedOpNames = ["*", "/", "+", "-"]}
                          )
-}

whiteSpace = P.whiteSpace lexer
lexeme     = P.lexeme lexer
symbol     = P.symbol lexer
natural    = P.natural lexer
parens     = P.parens lexer
semi       = P.semi lexer
identifier = P.identifier lexer
reserved   = P.reserved lexer
reservedOp = P.reservedOp lexer

--expr :: Parser Integer
expr = buildExpressionParser table factor <?> "expression"

-- for evaluating expressions
--table :: Integral a => OperatorTable String () Identity a
table = [[op "*" (*) AssocLeft, op "/" div AssocLeft]
        ,[op "+" (+) AssocLeft, op "-" (-) AssocLeft]
        ]
      where op s f assoc
               = Infix (do{ reservedOp s; return f} <?> "operator") assoc

factor = parens expr
         <|> natural
         <?> "simple expression"


{- -- for recognizing expressions and outputting text
   -- this section is not in the tutorial
strIn op = (\x y -> x ++ " " ++ op ++ " " ++ y)
mulStr = strIn "*"
divStr = strIn "/"
addStr = strIn "+"
subStr = strIn "-"

table = [[op "*" mulStr AssocLeft, op "/" divStr AssocLeft]
        ,[op "+" addStr AssocLeft, op "-" subStr AssocLeft]
        ]
      where op s f assoc
               = Infix (do{ reservedOp s; return f} <?> "operator") assoc

factor = parens expr
         <|> lexeme (many1 digit) -- natural
         <?> "simple expression"
-}

runLex :: Show a => Parser a -> String -> IO ()
runLex p input
    = run (do  whiteSpace
               x <-p
               eof
               return x
          ) input

price :: Parser Int -- price in cents
price = lexeme (do ds1 <- many1 digit
                   char '.'
                   ds2 <- count 2 digit
                   return (convert 0 (ds1 ++ ds2))
               )
        <?> "price"
        where
            convert n []     = n
            convert n (d:ds) = convert (10*n + digitToInt d) ds

{-
receipt :: Parser Bool
receipt = do ps <- many produkt
             p <- total
             return (sum ps == p)

produkt = do symbol "return"
             p <- price
             semi
             return (-p)
      <|> do identifier
             p <- price
             semi
             return p
      <?> "product"
-}

{-
total = do p <- price
           symbol "total"
           return p

produkt = do try (symbol "return")
             p <- price
             semi
             return (-p)
      <|> do identifier
             p <- price
             semi
             return p
      <?> "product"
 -}            

lexer :: P.TokenParser ()
lexer = P.makeTokenParser (haskellStyle
                               { P.reservedNames = ["return", "total"]
                               , P.reservedOpNames = ["*","/","+","-"]
                               }
                          )

receipt :: Parser Bool
receipt = do ps <- many produkt
             p <- total
             return (sum ps == p)

produkt = do reserved "return"
             p <- price
             semi
             return (-p)
      <|> do identifier
             p <- price
             semi
             return p
      <?> "produkt"

total = do p<- price
           reserved "total"
           return p
