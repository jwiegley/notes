{-# LANGUAGE LambdaCase #-}

module Dissolve where

import Data.Time

type Timestamp = UTCTime

type Duration = NominalDiffTime

data DissolveState
  = Dissolved {since :: Timestamp}
  | Dissolving {until :: Timestamp}
  | NotDissolving {delay :: Duration, since :: Timestamp}

isValidDissolveState :: Timestamp -> DissolveState -> Bool
isValidDissolveState now = \case
  Dissolved s -> s <= now
  Dissolving u -> now < u
  NotDissolving d s -> s <= now && d > 0

nextDissolveState :: Timestamp -> DissolveState -> DissolveState
nextDissolveState now = \case
  Dissolved s -> Dissolved s
  Dissolving u
    | now <= u -> Dissolved u
    | otherwise -> Dissolving u
  NotDissolving d s -> NotDissolving d s

startDissolving :: Timestamp -> DissolveState -> DissolveState
startDissolving now = \case
  Dissolved s -> Dissolved s
  Dissolving u -> Dissolving u
  NotDissolving d _ -> Dissolving (d `addUTCTime` now)

stopDissolving :: Timestamp -> DissolveState -> DissolveState
stopDissolving now = \case
  Dissolved s -> Dissolved s
  Dissolving u -> NotDissolving (u `diffUTCTime` now) now
  NotDissolving d s -> NotDissolving d s

ageSeconds :: Timestamp -> DissolveState -> Duration
ageSeconds now = \case
  Dissolved s -> now `diffUTCTime` s
  Dissolving _ -> 0
  NotDissolving _ s -> now `diffUTCTime` s

delaySeconds :: Timestamp -> DissolveState -> Duration
delaySeconds now = \case
  Dissolved _ -> 0
  Dissolving u -> u `diffUTCTime` now
  NotDissolving d _ -> d
