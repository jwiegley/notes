{-# LANGUAGE DeriveDataTypeable #-}

module IOAlternative where

import Control.Applicative
import Control.Exception
import Control.Exception.Enclosed
import Data.Typeable

data IOAlternativeEmpty = IOAlternativeEmpty deriving (Typeable, Show)

instance Exception IOAlternativeEmpty

instance Alternative IO where
    empty = throwIO IOAlternativeEmpty
    x <|> y = x `catchAny` \xe ->
        y `catchAny` \ye -> case fromException ye of
            Just IOAlternativeEmpty -> throwIO xe
            _ -> throwIO ye

main :: IO ()
main = do
    print =<< tryAny (putStrLn "one" <|> putStrLn "two")
    print =<< tryAny (error "oops" <|> putStrLn "two")
    print =<< tryAny (error "oops" <|> error "here" :: IO ())
    print =<< tryAny (putStrLn "one" <|> empty)
    print =<< tryAny (empty <|> putStrLn "two")
    print =<< tryAny (empty <|> empty :: IO ())
    print =<< tryAny (error "oops" <|> empty :: IO ())
    print =<< tryAny (empty <|> error "here" :: IO ())
