{-# LANGUAGE OverloadedStrings #-}

module Subtext where

import Data.List as L
import Data.Text as T

-- Search case-insensitivity for "leader" in "txt", and return all text after
-- it
findSubtextCPU :: Text -> Text -> Maybe Text
findSubtextCPU leader txt =
    case L.dropWhile (not . (leader `T.isPrefixOf`) . T.toLower) $ T.tails txt of
        [] -> Nothing
        (h:_) -> Just (T.drop (T.length leader) h)

-- Search case-insensitivity for "leader" in "txt", and return all text after
-- it
findSubtextMem :: Text -> Text -> Maybe Text
findSubtextMem leader txt =
    flip T.drop txt . (+ T.length leader)
      <$> locate (T.toLower leader) (T.toLower txt)
  where
      locate s t = L.findIndex (s `T.isPrefixOf`) (T.tails t)
