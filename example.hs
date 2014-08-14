{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}

module Main where

import Control.Exception
import Control.Policy
import Data.ByteString
import Data.List (isPrefixOf)
import Data.Monoid
import Data.Text
import Data.Text.Encoding

data FileReader = FileReader
type instance Policy FileReader = FilePath -> IO ByteString

data ConsoleDisplay = ConsoleDisplay
type instance Policy ConsoleDisplay = Text -> IO ()

goodFunction :: ( HasPolicy FileReader p
                , HasPolicy ConsoleDisplay p
                ) => DSL p ()
goodFunction = do
    contents <- FileReader # "/tmp/foo.txt"
    ConsoleDisplay # ("I read: " <> decodeUtf8 contents)

badFunction1 :: ( HasPolicy FileReader p
                , HasPolicy ConsoleDisplay p
                ) => DSL p ()
badFunction1 = do
    contents <- FileReader # "/foo.txt"
    ConsoleDisplay # ("I read: " <> decodeUtf8 contents)

badFunction2 :: ( HasPolicy FileReader p
                , HasPolicy ConsoleDisplay p
                ) => DSL p ()
badFunction2 = do
    contents <- FileReader # "/tmp/foo.txt"
    ConsoleDisplay # ("I read a secret: " <> decodeUtf8 contents)

main :: IO ()
main = do
    print =<< runPolicy goodFunction
    print =<< runPolicy badFunction1
    print =<< runPolicy badFunction2
  where
    runPolicy f = try $ executePolicy f policies :: IO (Either SomeException ())

    policies = (FileReader =: readInTmpOnly)
           :*: ((ConsoleDisplay =: filteredPrint)
           :*: Nil)

    readInTmpOnly path
        | "/tmp/" `Data.List.isPrefixOf` path =
            Data.ByteString.readFile path
        | otherwise = error $ "Attempted to read from: " ++ path

    filteredPrint str
        | "secret" `Data.Text.isInfixOf` str =
            error "Attempt to display secret data!"
        | otherwise = Prelude.putStrLn (Data.Text.unpack str)
