humanReadable :: Integer -> Integer -> Text
humanReadable den x =
    pack $ fromJust
          $ f 0 "b"
        <|> f 1 "K"
        <|> f 2 "M"
        <|> f 3 "G"
        <|> f 4 "T"
        <|> f 5 "P"
        <|> f 6 "X"
        <|> Just (printf "%db" x)
  where
    f :: Integer -> String -> Maybe String
    f n s | x < (den^succ n) =
        Just $ if n == 0
               then printf ("%d" ++ s) x
               else printf ("%." ++ show (min 3 (pred n)) ++ "f" ++ s)
                   (fromIntegral x / (fromIntegral den^n :: Double))
    f _ _ = Nothing
