{-# LANGUAGE DeriveDataTypeable #-}

module IOAlternative where

import Control.Applicative
import Control.Exception
import Control.Exception.Enclosed
import Data.Typeable

data EmptyException = EmptyException deriving (Typeable, Show)

instance Exception EmptyException

instance Alternative IO where
    empty = throwIO EmptyException
    x <|> y = x `catchAny` \xe ->
        y `catchAny` \ye -> case fromException ye of
            Just EmptyException -> throwIO xe
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
