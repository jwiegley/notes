import System.Random

flipCoin :: StdGen -> Bool
flipCoin gen = fst $ random gen

data Cat = Cat String deriving Show
data Probable a = Live a | Dead a deriving Show

fromProbable (Live a) = a
fromProbable (Dead a) = a

flipCat gen cat = if flipCoin gen 
                  then Live (fromProbable cat)
                  else Dead (fromProbable cat)

data Schroedinger a 
    = Opened (Probable a)
    | Unopened StdGen a deriving Show

instance Monad Schroedinger where
    Opened x >>= f = f x
    Unopened x y >>= f = f (Unopened x y)
    return x = Unopened (mkStdGen 100) x

main = do
  gen <- getStdGen
  print (Unopened gen (Cat "Felix") >>= return)
