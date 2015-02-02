import System.Random

flipCoin :: StdGen -> Bool
flipCoin gen = fst $ random gen

data Cat = Cat String deriving Show
data Schroedinger a = Live a | Dead a deriving Show

putInBox :: StdGen -> Cat -> Schroedinger Cat
putInBox gen x = if flipCoin gen then Live x else Dead x

main = do
  gen <- getStdGen
  print (putInBox gen (Cat "Felix"))
