module Dissolve where

data Duration = Duration

data Timestamp = Timestamp

data DissolveState
    = Dissolved { since :: Timestamp }
    | Dissolving { until :: Timestamp }
    | NotDissolving { delay :: Duration, since :: Timestamp }
