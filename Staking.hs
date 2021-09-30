{-# LANGUAGE NumericUnderscores #-}

module Journal.Staking where

import Control.Monad.State

oneDaySeconds, oneYearSeconds, oneMonthSeconds :: Double
oneDaySeconds = 24 * 60 * 60
oneYearSeconds = (4 * 365 + 1) * oneDaySeconds / 4
oneMonthSeconds = oneYearSeconds / 12

maxDissolveDelay :: Double
maxDissolveDelay = 8 * oneYearSeconds

maxAgeBonus :: Double
maxAgeBonus = 4 * oneYearSeconds

ytd :: Double -> Double
ytd = (* oneYearSeconds)

percentageOfSupply :: Double -> Double
percentageOfSupply s =
  (10 - (5 * (min s (8 * oneYearSeconds) / (8 * oneYearSeconds)))) / 100

data NNS = NNS
  { supply :: Double,
    votingPercentage :: Double,
    mintingPercentage :: Double,
    since :: Double
  }
  deriving (Show)

votingPower :: Double -> Double -> Double -> Double
votingPower stake delay age =
  let d = min delay maxDissolveDelay
      d_stake = stake + ((stake * d) / maxDissolveDelay)
      a = min age maxAgeBonus
   in d_stake + ((d_stake * a) / (4 * maxAgeBonus))

-- Compute rewards calculated on a given day
singleDay :: Double -> Double -> Double -> State NNS Double
singleDay stake delay age = do
  nns <- get
  let vp = votingPower stake delay age
      new = (supply nns * percentageOfSupply (since nns)) / 365.0
      earned = new * (vp / (supply nns * votingPercentage nns))
  put
    NNS
      { supply = supply nns + min earned (new * mintingPercentage nns),
        votingPercentage = votingPercentage nns,
        mintingPercentage = mintingPercentage nns,
        since = since nns + oneDaySeconds
      }
  pure earned

-- Given a set of starting conditions in terms of total supply of ICP, seconds
-- since genesis, an amount of ICP to be staked, a starting dissolve delay,
-- and a total time until disbursement, calculate what the final amount will
-- be assuming all other factors remain constant and all neuron holders merge
-- their maturity daily.
computeStake ::
  Double ->
  Double ->
  Double ->
  Double ->
  Double ->
  Double ->
  Double ->
  Double
computeStake
  initialStake
  votingPowerPerc
  mintingPerc
  startTime
  stake
  delay
  duration =
    evalState
      (go duration stake delay)
      (NNS initialStake votingPowerPerc mintingPerc startTime)
    where
      go t s d
        | t <= 0 = pure s
        | otherwise = do
          reward <- singleDay s d (if t < d then 0 else duration - t)
          go (t - oneDaySeconds) (s + reward) (min d t)

-- Result: ~403184
scenario :: Double
scenario =
  computeStake
    469_000_000
    0.67
    0.15
    (4 * oneMonthSeconds)
    100_000
    (8 * oneYearSeconds)
    (8 * oneYearSeconds)
