import System.Random

flipCoin :: StdGen -> Bool
flipCoin gen = fst $ random gen

data Cat = Cat String deriving Show
data Probable a = Live a | Dead deriving Show

fromProbable (Live a) = a
fromProbable Dead = Dead

flipCat :: StdGen -> Probable a -> Probable a
flipCat gen (Live cat) = if flipCoin gen 
                         then Live cat
                         else Dead
flipCat gen Dead = Dead

data Schroedinger a
    = Opened a
    | Unopened StdGen a deriving Show

fromTheBox (Opened a) = a
fromTheBox (Unopened _ a) = a

instance Monad Schroedinger where
    Opened Dead >>= _ = Opened Dead
    Opened (Live a) >>= f = f a
    Unopened y x >>= f = Opened (flipCat y x) >>= f
    return x = Unopened (mkStdGen 100) x

main = do
  gen <- getStdGen
  print (do
          box <- Unopened gen (Live (Cat "Felix"))
          -- The cat's fate is undecided
          return box)

