{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module VictorAssociatedTypes where

import Data.Proxy

class Manager m where
  type Ev m :: *

data Event = Event

data LocalManager = LocalManager

instance Manager LocalManager where
  type Ev LocalManager = Event

data RemoteManager = RemoteManager

instance Manager RemoteManager where
  type Ev RemoteManager = Event

data FondueEvent = FondueEvent

data IcEvent = IcEvent

type LogAnalyzer = IcEvent -> FondueEvent

data SegmentBox where
  Segment :: Manager m => Proxy m -> Ev m -> FondueEvent -> SegmentBox

passive_pipeline :: SegmentBox -> FondueEvent
passive_pipeline = undefined

data Option = Local | Remote

plugPassive :: Manager m => m -> (Ev m -> FondueEvent) -> ()
plugPassive = undefined

main :: IO ()
main = do
  let optManagerType = undefined
  let localManager :: LocalManager = undefined
  let remoteManager :: RemoteManager = undefined
  let man = case optManagerType of
        Local -> localManager
        Remote -> remoteManager
  plugPassive man passive_pipeline
