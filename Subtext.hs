{-# LANGUAGE OverloadedStrings #-}

module Subtext where

import Data.List as L
import Data.Text as T

-- Search case-insensitivity for "leader" in "txt", and return all text after
-- it
findSubtext :: Text -> Text -> Maybe Text
findSubtext leader txt =
    flip T.drop txt . (+ T.length leader)
      <$> locate (T.toLower leader) (T.toLower txt)
  where
      locate s t = L.findIndex (s `T.isPrefixOf`) (T.tails t)
