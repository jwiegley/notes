import qualified Data.ByteString.Lazy.Char8 as BS
import System.Environment

main = do
  args <- getArgs
  BS.putStr $ BS.intercalate (BS.pack "\0") 
    $ filter (not . BS.isPrefixOf (BS.pack "-Wl,-rpath"))
    $ map BS.pack args
