{-# LANGUAGE BangPatterns, DeriveFunctor, RankNTypes, ScopedTypeVariables #-}

module Main where

import qualified Data.Map as M
import qualified Data.Vector as V
import Control.Applicative
import Control.DeepSeq
import Control.Monad.Fix
import Control.Monad.Free
import Data.Map (Map)
import System.Random
import Text.Printf


newtype Prob a = Prob (forall g. (RandomGen g) => g -> (a, g))
    deriving (Functor)

type MC = Free Prob


stepMC :: (RandomGen g) => g -> MC a -> (a, g)
stepMC g' (Pure x) = (x, g')
stepMC g' (Free (Prob f)) =
    let (c, g) = f g' in
    stepMC g c


simulate :: forall a g. (NFData a, Ord a, RandomGen g) => Int -> g -> MC a -> (Map a Int, g)
simulate count g' c = loop M.empty count g'
    where
    loop :: Map a Int -> Int -> g -> (Map a Int, g)
    loop m' 0 g' = (m', g')
    loop !m' n !g' =
        let (x, g) = stepMC g' c in
        (loop $!! M.insertWith (+) x 1 m') (n - 1) g


simulateIO :: (NFData a, Ord a, RandomGen g, Show a) => Int -> g -> MC a -> IO ()
simulateIO count g' =
    mapM_ (\(x, p) -> printf "%s: %7d (%0.6f)\n" (show x) p (fromIntegral p / d)) .
    M.assocs .
    fst .
    simulate count g'

    where
    d :: Double
    d = fromIntegral count


uniform :: [a] -> MC a
uniform xs' =
    let xs = V.fromList xs' in
    liftF $ Prob $ \g' ->
        let (i, g) = randomR (0, V.length xs - 1) g'
            x = xs V.! i
        in (x, g)


main :: IO ()
main = do
    g <- getStdGen
    simulateIO 100000 g $ do
        x <- uniform [0..2]
        if x == 1
          then return "x"
          else do
              y <- uniform ['a'..'w']
              return (y : "blah")
