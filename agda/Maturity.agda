module Maturity where

open import Data.Bool hiding (_≤_; _≟_)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤ᵇ_; _≤_)
open import Data.Rational.Properties hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Relation.Nullary using (does; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

Seconds = ℕ

Timestamp = ℕ

sevenDays : Seconds
sevenDays = 86400 Data.Nat.* 7
  where
    open import Data.Nat

E8s = ℚ

Percentage = ℚ

------------------------------------------------------------------------

record NeuronOld : Set where
  constructor neuronold
  field
    stake    : E8s
    maturity : E8s   

mergeMaturity : NeuronOld → NeuronOld
mergeMaturity n =
  record { stake    = stake n + maturity n
         ; maturity = 0ℚ }
  where
    open NeuronOld

-- Returns the modified parent neuron and the spawned reward neuron.
spawnMaturity : NeuronOld → Percentage → NeuronOld × NeuronOld
spawnMaturity n perc =
  ( record { stake    = stake n
           ; maturity = maturity n - amount }
  , record { stake    = amount
           ; maturity = 0ℚ }
  )
  where
    open NeuronOld

    amount : ℚ
    amount = NeuronOld.maturity n * perc

-- Given a dissolved reward neuron, claim it. Returns the resulting neuron and
-- the ICP to transfer to the neuron holder's primary account.
claimIcpOld : Timestamp → NeuronOld → NeuronOld × E8s
claimIcpOld _ (neuronold s m) = ( neuronold 0ℚ 0ℚ , s + m )

receiveRewardOld : E8s → NeuronOld → NeuronOld
receiveRewardOld reward (neuronold s m) = neuronold s (m + reward)

------------------------------------------------------------------------

record Neuron : Set where
  constructor neuron
  field
    stake             : E8s
    stakedMaturity    : E8s
    maturity          : E8s
    isCompounding     : Bool
    -- Amount of available maturity that can be used to produce ICP
    availableMaturity : Timestamp → E8s

open Neuron

-- Process to convert and old-style Neuron the new model
upgrade : NeuronOld → Neuron
upgrade (neuronold s m) =
  record { stake             = s
         ; stakedMaturity    = 0ℚ
         ; maturity          = m
         ; isCompounding     = false
         ; availableMaturity = λ _ → 0ℚ }

stakeMaturity : Neuron → Neuron
stakeMaturity n =
  record n { stakedMaturity = stakedMaturity n + maturity n
           ; maturity       = 0ℚ }

effectiveStake : Neuron → E8s
effectiveStake n = stake n + stakedMaturity n

-- Disburse maturity requests that ICP be produced from maturity
disburseMaturity : Timestamp → Neuron → Neuron
disburseMaturity now n =
  record n { maturity          = 0ℚ
           ; availableMaturity = λ t → 
               availableMaturity n t +
                 (if now Data.Nat.+ sevenDays Data.Nat.≤ᵇ t
                  then maturity n
                  else 0ℚ)
           }

exchangeMaturity : Neuron → Maybe (Neuron × E8s)
exchangeMaturity n =
  if maturity n ≤ᵇ stake n
  then just ( record n { stake          = stake n - maturity n
                       ; stakedMaturity = stakedMaturity n + maturity n
                       ; maturity       = 0ℚ }
            , maturity n
            )
  else nothing

claimIcp : Timestamp → Neuron → Neuron × E8s
claimIcp now n =
  ( record n { availableMaturity = λ t →
                 availableMaturity n t - availableMaturity n now }
  , availableMaturity n now
  )

receiveReward : E8s → Neuron → Neuron
receiveReward reward n =
  if isCompounding n
  then record n { maturity       = maturity n       + reward }
  else record n { stakedMaturity = stakedMaturity n + reward }

stake-upgrade : ∀ {o} → stake (upgrade o) ≡ NeuronOld.stake o
stake-upgrade = refl

maturity-upgrade : ∀ {o} → maturity (upgrade o) ≡ NeuronOld.maturity o
maturity-upgrade = refl

effectiveStake-unfold : ∀ {n o} 
  → stake n + stakedMaturity n ≡ stake o + stakedMaturity o
  → effectiveStake n ≡ effectiveStake o
effectiveStake-unfold = id

helper-lemma : ∀ {x y} → x + y + 0ℚ ≡ x + (0ℚ + y)
helper-lemma {x} {y} rewrite +-identityˡ y | +-identityʳ (x + y) = refl

stake-merge : ∀ o → effectiveStake (upgrade (mergeMaturity o)) ≡ 
                    effectiveStake (stakeMaturity (upgrade o))
stake-merge o =
  effectiveStake-unfold 
    {(upgrade (mergeMaturity o))}
    {(stakeMaturity (upgrade o))} 
    (helper-lemma {NeuronOld.stake o} {NeuronOld.maturity o})
