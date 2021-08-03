{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NumericUnderscores #-}

module Governance where

import Data.Set hiding (split)
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

-- The age can be larger than what contributes to the bonus, to provide a
-- hidden incentive for increasing stake or dissolve delay.
newtype Duration = Duration {getDuration :: Int}
  deriving (Eq, Ord, Num, Show)

one_month :: Duration
one_month = Duration 2_629_800

six_months :: Duration
six_months = one_month * 6

one_year :: Duration
one_year = one_month * 12

four_years :: Duration
four_years = one_year * 4

eight_years :: Duration
eight_years = one_year * 8

twenty_years :: Duration
twenty_years = one_year * 20

genDuration :: Gen Duration
genDuration = fmap Duration . Gen.int $ Range.linear 0 (getDuration twenty_years)

data DissolveState
  = NonDissolved {delay :: Duration, age :: Duration}
  | Dissolving {delay :: Duration}
  | Dissolved {age :: Duration}
  deriving (Eq, Ord, Show)

genDissolveState :: Gen DissolveState
genDissolveState =
  Gen.choice
    [ NonDissolved <$> genDuration <*> genDuration,
      Dissolving <$> genDuration,
      Dissolved <$> genDuration
    ]

dissolve_delay :: DissolveState -> Duration
dissolve_delay (NonDissolved d _) = d
dissolve_delay (Dissolving d) = d
dissolve_delay (Dissolved _) = 0

current_age :: DissolveState -> Duration
current_age (NonDissolved _ a) = a
current_age (Dissolving _) = 0
current_age (Dissolved a) = a

max_age_for_bonus :: Duration
max_age_for_bonus = 1 -- 4 years

max_dissolve_delay :: Duration
max_dissolve_delay = 1 -- 8 years

newtype ICP = ICP {getICP :: Int}
  deriving (Eq, Ord, Num, Show)

data Neuron = Neuron
  { stake :: ICP,
    maturity :: ICP,
    dissolve_state :: DissolveState
  }
  deriving (Eq, Ord, Show)

genNeuron :: Gen Neuron
genNeuron = undefined

merge :: Neuron -> Neuron -> Neuron
merge = undefined

split :: ICP -> Neuron -> (Neuron, Neuron)
split = undefined

disburse :: Neuron -> ICP
disburse = undefined

create :: ICP -> Neuron
create = undefined

refresh :: Neuron -> ICP -> Neuron
refresh = undefined

increase_dissolve_delay :: Neuron -> ICP -> Neuron
increase_dissolve_delay = undefined

voting_power :: Set Neuron -> ICP
voting_power = undefined

-- Return True if two sets of neurons are equivalent in the following sense,
-- up to transaction fees:
--
-- - Same maturity
-- - Same stake
-- - Same age bonus
-- - Same hidden age incentive
-- - Same voting power
(~~) :: Set Neuron -> Set Neuron -> Bool
(~~) _xs _ys = undefined

test_merge_split :: Property
test_merge_split = property $ do
  x <- forAll genNeuron
  y <- forAll genNeuron
  split (stake y) (merge x y) === (x, y)

-- test_split_merge :: Property
-- test_split_merge = (merge . split ~~ id)

-- test_stake_disburse :: Property
-- test_stake_disburse = (disburse . stake ~~ id)

-- test_disburse_stake :: Property
-- test_disburse_stake = (stake . disburse ~~ id)

test_disburse_all :: Property
test_disburse_all = property $ do
  x <- forAll genNeuron
  stake (snd (split (stake x) x)) === disburse x

start_dissolving :: Neuron -> ICP -> Neuron
start_dissolving = undefined

stop_dissolving :: Neuron -> ICP -> Neuron
stop_dissolving = undefined
