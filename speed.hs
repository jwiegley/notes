module Speed where

import Data.List
import qualified Data.ByteString as BS

foo f z = foldl' f z . BS.unpack

bar f z = BS.foldl' f z
