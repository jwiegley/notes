module Amount where

import Ratio
import Numeric
import qualified Data.Map as Map

{-
  A Commodity is just a name, which looks up a CommodityDetails value within a
  CommodityPool.  The reason it must be only a name is that the details it
  refers to may alter as new amounts are parsed.
 -}
type Commodity = String

data CommodityDetails = CommodityDetails {
      symbol         :: String,
      dispPrecision  :: Int,
      separated      :: Bool,
      thousandsMarks :: Bool,
      prefixed       :: Bool
    }

data CommodityPool = CommodityPool (Map.Map Commodity CommodityDetails)

type BigNum = Ratio Integer

data Amount = Amount {
      quantity     :: BigNum,
      commodity    :: Commodity,
      intPrecision :: Int
    } deriving (Show)

instance Eq Amount where
    x == y = quantity x  == quantity y && 
             commodity x == commodity y

trueZero :: Amount -> Bool
trueZero x = quantity x == 0

{- jww (2009-03-26): So how do I reference the CommodityPool here? -}
zero :: Amount -> Bool
zero x = any (>0) $ take prec fracDigits
    where prec       = 2 -- dispPrecision $ lookupCommodity (commodity x)
          digits     = floatToDigits 10 $ (fromRational (quantity x) :: Double)
          fracDigits = drop (snd digits) (fst digits)

data Session a = Session a

instance Monad Session where
    Session x >>= f = f x
    return x = Session x

lookupCommodity :: String -> Session CommodityDetails
lookupCommodity sym = undefined

zero2 :: Amount -> Session Bool
zero2 x = do
  comm <- lookupCommodity (commodity x)
  let prec       = dispPrecision comm
      digits     = floatToDigits 10 $ (fromRational (quantity x) :: Double)
      fracDigits = drop (snd digits) (fst digits)
  return $ any (>0) $ take prec fracDigits

foo :: Amount
foo = Amount (3300 % 10000000) "$" 6

bar :: Amount
bar = foo

baz :: Bool
baz = foo == bar
