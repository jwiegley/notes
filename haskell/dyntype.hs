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
import Data.Data.Lens

main :: IO ()
main = do
  str <- B.readFile "test.yaml"
  case Y.decode str of
    Nothing   -> error "Failed to parse"
    Just yaml ->
      print $ (yaml ^. key "tree" .folded .to _array
                    ^..traverse .to findUrl .folded
               :: [Either Text (Text,Text)])

  where
    _array :: Value -> [Value]
    _array (Array a) = V.toList a
    _array _ = []

    findUrl v = do
        let mv = Just v
        typ <- mv ^. key "type"
        url <- mv ^. key "url"
        case typ :: Text of
          "tree" -> Just (Left url)
          "blob" -> do
            path <- mv ^. key "path" . asText
            Just (Right (url, path))
          _ -> Nothing

-- where test.yaml is the following:
--
-- {
--   "sha": "9fb037999f264ba9a7fc6274d15fa3ae2ab98312",
--   "url": "https://api.github.com/repo/octocat/Hello-World/trees/9fb037999f264ba9a7fc6274d15fa3ae2ab98312",
--   "tree": [
--     {
--       "path": "file.rb",
--       "mode": "100644",
--       "type": "blob",
--       "size": 30,
--       "sha": "44b4fc6d56897b048c772eb4087f854f46256132",
--       "url": "https://api.github.com/octocat/Hello-World/git/blobs/44b4fc6d56897b048c772eb4087f854f46256132"
--     },
--     {
--       "path": "subdir",
--       "mode": "040000",
--       "type": "tree",
--       "sha": "f484d249c660418515fb01c2b9662073663c242e",
--       "url": "https://api.github.com/octocat/Hello-World/git/blobs/f484d249c660418515fb01c2b9662073663c242e"
--     },
--     {
--       "path": "exec_file",
--       "mode": "100755",
--       "type": "blob",
--       "size": 75,
--       "sha": "45b983be36b73c0788dc9cbcb76cbb80fc7bb057",
--       "url": "https://api.github.com/octocat/Hello-World/git/blobs/45b983be36b73c0788dc9cbcb76cbb80fc7bb057"
--     }
--   ]
-- }