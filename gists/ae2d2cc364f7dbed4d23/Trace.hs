parseWord = many1 (satisfy (not . stopChar)) <* skipWhitespace

skipWhitespace = skipMany (satisfy isWhitespace)

endOfLine :: Word8 -> Bool
endOfLine c = c == 13 || c == 10

isWhitespace :: Word8 -> Bool
isWhitespace c
    =  c == 32  || c == 9
    || (c == 123 || c == 125) -- {}
    || (c == 40  || c == 41)  -- ()
    || (c == 91  || c == 93)  -- []
    || (c == 124 || c == 44)  -- |,

stopChar :: Word8 -> Bool
stopChar c
    =  endOfLine c          -- newline
    ||  isWhitespace c       -- space
    ||  c == 35              -- #
    ||  c == 43              -- +
    ||  c == 58              -- :
