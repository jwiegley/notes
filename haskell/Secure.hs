{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

import Data.Type.Equality

data AuthLevel = Public | Secret

data Sing (t :: AuthLevel) where
    SPublic :: Sing 'Public
    SSecret :: Sing 'Secret

doPublicComputation :: l ~ 'Public => Sing l -> IO ()
doPublicComputation = undefined

doSecureComputation :: l ~ 'Secret => Sing l -> IO ()
doSecureComputation = undefined

authenticated :: (Sing 'Public -> IO ())
              -> (Sing 'Secret -> IO ())
              -> IO ()
authenticated whenPublic whenSecret = whenPublic SPublic

-- This gives the error:
-- Couldn't match type ‘'Secret’ with ‘'Public’
--   Expected type: Sing 'Public -> IO ()
--     Actual type: Sing 'Secret -> IO ()
executor :: IO ()
executor = authenticated doSecureComputation doPublicComputation

main = executor
