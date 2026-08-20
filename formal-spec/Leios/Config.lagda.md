## Leios.Config

This module defines the configuration parameters for the Leios protocol.
It includes block type definitions (Input Blocks, Endorser Blocks, Votes)
and protocol parameters such as party counts, stake distribution,
stage length, and winning slot specifications.
<!--
```agda
{-# OPTIONS --safe #-}
```
-->
```agda
open import Leios.Prelude
open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Leios.Config where

data BlockType : Type where
  IB EB VT : BlockType

unquoteDecl DecEq-BlockType = derive-DecEq ((quote BlockType , DecEq-BlockType) ∷ [])

record NetworkParams : Type where
  field numberOfParties   : ℕ
        stakeDistribution : TotalMap (Fin numberOfParties) ℕ
        ⦃ NonZero-numberOfParties ⦄ : NonZero numberOfParties

record Params : Type where
  field networkParams    : NetworkParams
        Lhdr Lvote Ldiff : ℕ
        -- CIP-0164 committee stake coverage σc, as a ratio σc-num / σc-den
        -- (e.g. 99 / 100): the voting committee is the stake-descending
        -- prefix of pools whose cumulative stake reaches σc of the total.
        σc-num σc-den    : ℕ

  open NetworkParams networkParams public

module _ (params : Params) where
  open Params params

  private
    allStakes : List ℕ
    allStakes = L.tabulate (TotalMap.lookup stakeDistribution)

    totalStake : ℕ
    totalStake = L.sum allStakes

    -- stake held by pools with strictly more stake than the given one
    richerStake : ℕ → ℕ
    richerStake st = L.sum (L.filter (st <?_) allStakes)

  -- Voting-committee membership by stake-based truncation (CIP-0164,
  -- "Committee Structure"): order pools by stake descending and accumulate
  -- until the cumulative stake covers the σc target; the committee is fixed
  -- for the whole epoch. A pool with stake `st` is on the committee iff the
  -- pools with strictly more stake do not already cover the target. Pools of
  -- equal stake at the boundary are all included (the CIP fixes no tie
  -- order).
  inVotingCommittee : ℕ → Type
  inVotingCommittee st = richerStake st * σc-den < totalStake * σc-num

record TestParams (params : Params) : Type where
  open Params params

  field sutId : Fin numberOfParties
        winning-slots : ℙ ℕ
```
