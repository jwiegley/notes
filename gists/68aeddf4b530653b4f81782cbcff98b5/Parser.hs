skipLineComment' :: Tokens Text -> Parser ()
skipLineComment' prefix =
  string prefix
      *> void (takeWhileP (Just "character") (\x -> x /= '\n' && x /= '\r'))

whiteSpace :: Parser ()
whiteSpace = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = skipLineComment' "#"
    blockCmnt = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme p = p <* whiteSpace

space' :: Parser (Tokens Text)
space' = takeWhileP (Just "white space") isSpace

space1' :: Parser (Tokens Text)
space1' = takeWhile1P (Just "white space") isSpace

lineComment' :: Tokens Text -> Parser (Tokens Text)
lineComment' prefix =
  string prefix
      *> takeWhileP (Just "character") (\x -> x /= '\n' && x /= '\r')

blockComment'
  :: Tokens Text                 -- ^ Start of block comment
  -> Tokens Text                 -- ^ End of block comment
  -> Parser (Tokens Text)
blockComment' start end =
    C.string start *> (pack <$> manyTill anySingle (C.string end))

whiteSpaceSyntax :: Parser (NSyntax a)
whiteSpaceSyntax = fmap mconcat $ many $ choice
    [ Fix . NSynSpace <$> hidden space1'
      -- jww (2019-03-09): Strip out the comment leaders from 't'
    , (\t -> Fix (NSynOrig t (Fix (NSynLineComment t)))) <$> hidden lineCmnt
    , (\t -> Fix (NSynOrig t (Fix (NSynBlockComment t)))) <$> hidden blockCmnt
    ]
  where
    lineCmnt  = lineComment' "#"
    blockCmnt = blockComment' "/*" "*/"

exprSyntax :: Parser a -> Parser (NSyntax a)
exprSyntax = fmap (Fix . NSynExpr)

lexemeSyntax :: Parser a -> Parser (NSyntax a)
lexemeSyntax p = fmap Fix $ NSynGlue <$> exprSyntax p <*> whiteSpaceSyntax
