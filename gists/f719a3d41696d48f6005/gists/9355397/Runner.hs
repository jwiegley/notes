newtype WrappedUTCTime = WrappedUTCTime { unWrappedUTCTime :: UTCTime }
    deriving (Eq, Read, Show, Data, Typeable, Ord,
              Serialize, Generic, Hashable)

toPicoSeconds :: UTCTime -> Integer
toPicoSeconds t = numerator x
  where
    x     = toRational day * 86400 * pico + psecs * pico
    day   = toModifiedJulianDay (utctDay t)
    psecs = toRational (utctDayTime t)
    pico  = 10^(12 :: Integer)

fromPicoSeconds :: Integer -> UTCTime
fromPicoSeconds x = UTCTime (ModifiedJulianDay dayPart) (fromRational psecs)
  where
    dayPart = x `div` day
    day     = 86400 * pico
    psecs   = (toRational x - toRational dayPart * fromIntegral day)
                  / fromIntegral pico
    pico    = 10^(12 :: Integer)

instance Serialize UTCTime where
    put = put . toPicoSeconds
    get = fmap fromPicoSeconds get

instance Hashable UTCTime where
    hash t = hash (toPicoSeconds t)
    hashWithSalt x t = hashWithSalt x (toPicoSeconds t)

instance ToJSON WrappedUTCTime where
    toJSON (WrappedUTCTime t) = toJSON (toPicoSeconds t)
instance FromJSON WrappedUTCTime where
    parseJSON o = WrappedUTCTime . fromPicoSeconds <$> parseJSON o
