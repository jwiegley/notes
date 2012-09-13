import System.Random

flipCoin :: StdGen -> Bool
flipCoin gen = fst $ random gen

data Cat = Cat String deriving Show
data Probable a = Live a | Dead a deriving Show

fromProbable (Live a) = a
fromProbable (Dead a) = a

flipCat gen cat = if flipCoin gen 
                  then Live cat
                  else Dead cat

data Schroedinger a
    = Opened a
    | Unopened StdGen a deriving Show

instance Monad Schroedinger where
    Opened x >>= f = f x
    Unopened y x >>= f = f $ flipCat y x
    return x = Unopened (mkStdGen 100) x

main = do
  gen <- getStdGen
  print (do
          box <- Unopened gen (Live (Cat "Felix"))
          -- The cat's fate is undecided
          return box)
