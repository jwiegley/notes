module Serial where

import Control.Lens
import Data.Binary
import Data.ByteString.Lazy

binary :: Binary a => Prism' ByteString a
binary = prism encode $ \bs -> case decodeOrFail bs of
    Left  (_bs, _off, _err) -> Left bs
    Right (_bs, _off, x)    -> Right x
