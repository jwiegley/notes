-- | Returns (Just n) if n encodeable as an int in SAFE, and Nothing otherwise
encodeSAFEInt :: SAFEInt Int -> Maybe Int
encodeSAFEInt (SAFEInt n)
  | n == minSAFEInt = Nothing
  | otherwise = Just (abs n)
