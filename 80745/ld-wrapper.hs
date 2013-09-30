import Data.List
import System.Environment

main = do
  args <- getArgs
  putStr $ intercalate "\0" $ filter (not . isPrefixOf "-Wl,-rpath") args
