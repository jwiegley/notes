{-# LANGUAGE OverloadedStrings #-}

module Subtext where

import Data.Text (Text)
import qualified Data.Text as T

-- Search case-insensitivity for "leader" in "txt", and return all text after
-- it
findSubtext :: Text -> Text -> Maybe Text
findSubtext leader txt =
    case dropWhile (not . (leader `T.isPrefixOf`) . T.toLower) $ T.tails txt of
        [] -> Nothing
        (h:_) -> Just (T.drop (T.length leader) h)
