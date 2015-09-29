import Control.DeepSeq
import Numeric.Probability.Distribution
import Control.Monad
import Data.List

f 1 = fromFreqs [(1, 0.3), (2, 0.7)]
f 2 = fromFreqs [(1, 0.5), (2, 0.5)]

nospaceleak =
  foldl' (\x y -> force (norm' (x >>= y))) (f 1)
      $ replicate 25 f   :: T Float Int

main = print nospaceleak
