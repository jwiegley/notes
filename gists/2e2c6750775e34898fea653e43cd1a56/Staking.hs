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

-- From https://docs.google.com/document/d/1wP7zEcWdb2hE7L7of2Zhf6LxbWOqWnKGQ6LdIlDPzsk/edit
-- R(t) = Rf + (R0-Rf) [ (t-T) / (G-T) ]^2
percentageOfSupply :: Double -> Double
percentageOfSupply t =
  0.05 + (0.1 - 0.05) * (((t - nT) / (nG - nT)) ** 2.0)
  where
    nG = 0
    nT = 8 * oneYearSeconds

data NNS = NNS
  { totalSupply :: Double,
    votingPercentage :: Double,
    mintingPercentage :: Double,
    since :: Double
  }
  deriving (Show)

votingPower :: Double -> Double -> Double -> Double
votingPower _ delay _ | delay < 6 * oneMonthSeconds = 0
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
      dailyPercentage = percentageOfSupply (since nns) / 365.0
      dailyReward = totalSupply nns * dailyPercentage
      fraction = vp / (totalSupply nns * votingPercentage nns)
      earned = dailyReward * fraction
      -- Another way of writing 'earned' is the following, which shows that if
      -- the voting population keeps pace with the increase in supply, one's
      -- daily take remains the same.
      -- earned' = dailyPercentage * (vp / votingPercentage nns)
      minted = max earned (dailyReward * mintingPercentage nns)
  put
    nns
      { totalSupply = totalSupply nns + minted,
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
scenario :: IO ()
scenario = do
  putStrLn "1,000 ICP"
  putStrLn $ "dissolve delay 8, dissolving in 8  = " ++ show (compute 8 8)
  putStrLn $ "dissolve delay 8, dissolving in 12 = " ++ show (compute 8 12)
  putStrLn $ "dissolve delay 4, dissolving in 8  = " ++ show (compute 4 8)
  putStrLn $ "dissolve delay 4, dissolving in 12 = " ++ show (compute 4 12)
  where
    compute delay duration =
      computeStake
        469_000_000
        0.67
        0.15
        (5 * oneMonthSeconds)
        1_000
        (delay * oneYearSeconds)
        (duration * oneYearSeconds)
