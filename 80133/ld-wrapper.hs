import System.Environment
import Text.Regex.Posix

xlat :: [String] -> [String]
xlat [] = []
xlat (x:xs) = xlat' (x =~ regex :: (String,String,String,[String]))
    where regex = "-Wl,-rpath,(.+)"
          xlat' (_, _, _, []) = x : xlat xs
          xlat' (_, _, _, (y:ys)) = "-rpath" : y : xlat xs

main = do
  args <- getArgs
  print $ xlat args
