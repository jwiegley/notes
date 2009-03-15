import System.Random

flipCoin :: StdGen -> Bool
flipCoin gen = fst $ random gen

data Cat = Cat String deriving Show
data Probable a = Live a | Dead a deriving Show

fromProbable (Live a) = a
fromProbable (Dead a) = a

flipCat :: StdGen -> Probable a -> Probable a
flipCat gen cat = if flipCoin gen 
                  then Live (fromProbable cat)
                  else Dead (fromProbable cat)

data Schroedinger a
    = Opened a
    | Unopened StdGen a deriving Show

fromTheBox (Opened a) = a
fromTheBox (Unopened _ a) = a

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

