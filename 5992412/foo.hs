import Data.Conduit
import Data.Conduit.List

fileLister :: FilePath -> Source IO FilePath
fileLister dir = do
    enumerator <- lift $ fileEnumerateChildren dir "*" [] Nothing
    whileJust (fileEnumeratorNextFile enumerator Nothing) yield

main :: IO ()
main = do
  glibTypeInit
  src <- fileLister "/usr/bin"
  src $$ do
      file1 <- await
      file2 <- await
      print file1
      print file2
