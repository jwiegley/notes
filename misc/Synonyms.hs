{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Synonyms where

import Control.Monad.Free

data TeletypeF r = GetF (String -> r) | PutF String r
    deriving Functor

newtype Teletype a = Teletype { runTeletype :: Free TeletypeF a }
    deriving (Functor, Applicative, Monad, MonadFree TeletypeF)

get :: Teletype String
get = liftF (GetF id)

put :: String -> Teletype ()
put s = liftF (PutF s ())

pattern Get :: (String -> Teletype a) -> Teletype a
pattern Get x <- Teletype (Free (GetF (fmap Teletype -> x)))

pattern Put :: String -> Teletype a -> Teletype a
pattern Put s r <- Teletype (Free (PutF s (Teletype -> r)))

main :: IO ()
main = do
    let action = do x <- get
                    put x
    case action of
        Get (($ "hello") -> Put "hello" _) -> putStrLn "deconstructed"

        Get _   -> putStrLn "Found Get"
        Put _ _ -> putStrLn "Found Put"

        _ -> error "Pattern synonyms lead to exhaustion check warnings"
