{-# LANGUAGE OverloadedStrings #-}

import Control.Applicative
import Control.Lens
import Data.Aeson as A
import Data.Aeson.Lens
import Data.ByteString as B
import Data.ByteString.Lazy as BL
import Data.Text as T
import Data.Yaml as Y
import Data.Maybe
import qualified Data.Vector as V

main :: IO ()
main = do
  str <- B.readFile "test.yaml"
  case Y.decode str of
    Nothing   -> error "Failed to parse"
    Just yaml ->
      print $ (yaml ^. key "tree" .folded .to _array ^..folded ._blobTree
               :: [Either Text (Text,Text)])

  where
    _array :: Value -> [Value]
    _array (Array a) = V.toList a
    _array _ = []

    _blobTree :: Traversal Value (Either Text (Text,Text))
                 (Either Text (Text,Text)) (Either Text (Text,Text))
    _blobTree f v
      | Just r <- findUrl v = f r
      | otherwise = pure (Left "")

    findUrl v = do
        let mv = Just v
        typ <- mv ^. key "type"
        url <- mv ^. key "url"
        case typ :: Text of
          "tree" -> Just (Left (fromJust url))
          "blob" -> do
            path <- mv ^. key "path" . asText
            Just (Right (fromJust url, path))
          _ -> Nothing