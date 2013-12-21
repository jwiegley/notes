import System.Random

flipCoin :: StdGen -> Bool
flipCoin gen = fst $ random gen

data Cat = Cat String deriving Show
data Probable a = Live a | Dead deriving Show

flipCat :: StdGen -> a -> Probable a
flipCat gen cat = if flipCoin gen 
                  then Live cat
                  else Dead

data Schroedinger a
    = Opened (Probable a)
    | Unopened StdGen a deriving Show

instance Monad Schroedinger where
    Opened Dead >>= _ = Opened Dead
    Opened (Live a) >>= f = f a
    Unopened y x >>= f = Opened (flipCat y x) >>= f
    return x = Opened (Live x)

main = do
  gen <- getStdGen
  print (do
          box <- Unopened gen (Cat "Felix")
          -- The cat's fate is undecided
          return box)
