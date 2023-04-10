{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}

module Main (main) where

import GHC.Natural (Natural(..))
import GHC.Num.BigNat
import GHC.TypeNats (KnownNat, natVal)
import GHC.Exts ((<=#), isTrue#, minusWord#)

newtype Mod m = Mod Natural deriving (Show)

negateMod :: Natural -> Natural -> Natural
negateMod _ (NatS# 0##) = NatS# 0##
negateMod (NatS# m#) (NatS# x#) = NatS# (m# `minusWord#` x#)
negateMod NatS#{} _ = error "argument is larger than modulus"
negateMod (NatJ# (BN# m#)) (NatS# x#) = bigNatToNat (m# `bigNatSubWordUnsafe#` x#)
negateMod (NatJ# (BN# m#)) (NatJ# (BN# x#)) = bigNatToNat (m# `bigNatSubUnsafe` x#)

bigNatToNat :: BigNat# -> Natural
bigNatToNat r# =
  if isTrue# (bigNatSize# r# <=# 1#) then NatS# (bigNatToWord# r#) else NatJ# (BN# r#)

negate_ :: KnownNat m => Mod m -> Mod m
negate_ mx@(Mod x) = Mod $ negateMod (natVal mx) x

fromInteger_ :: KnownNat m => Integer -> Mod m
fromInteger_ x = mx
    where
      mx = Mod $ fromInteger $ x `mod` toInteger (natVal mx)

main :: IO ()
main = do
    print (negate_ (fromInteger_ 1 :: Mod 18446744073709551616))
    let x = (negate_ (fromInteger_ 1 :: Mod 18446744073709551616)) in print x
