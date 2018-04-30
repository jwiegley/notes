module GenericClosure where

import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as M
import           Data.HashSet (HashSet)
import qualified Data.HashSet as S
import           Data.Text (Text)
import qualified Data.Text as T

genericClosure :: [HashMap Text a]
               -> HashSet Text
               -> (HashMap Text a -> [HashMap Text a])
               -> [HashMap Text a]
genericClosure startSet keys operator = do
    (startSet ++) $ concat $ flip map startSet $ \m -> do
        let args = M.fromList $
                concatMap (\key ->
                           case M.lookup key m of
                               Nothing -> []
                               Just v  -> [(key, v)])
                      (S.toList keys)
        genericClosure (operator args) keys operator
