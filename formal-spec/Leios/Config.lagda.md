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
        stake-support-nonEmpty : ∃[ i ] NonZero (TotalMap.lookup stakeDistribution i)

  instance
    NonZero-numberOfParties : NonZero numberOfParties
    NonZero-numberOfParties = F.nonZeroIndex (proj₁ stake-support-nonEmpty)

record Params : Type where
  field networkParams    : NetworkParams
        Lhdr Lvote Ldiff : ℕ
        σc               : ℚ

  open NetworkParams networkParams public

module _ (params : Params) where
  open Params params

  private
    allStakes : List ℕ
    allStakes = L.tabulate (TotalMap.lookup stakeDistribution)

    totalStake : ℕ
    totalStake = L.sum allStakes

    instance
      totalStake-nonZero : NonZero totalStake
      totalStake-nonZero = tabulate-sum-nonZero (TotalMap.lookup stakeDistribution) stake-support-nonEmpty
        where
          elem≤tabulate-sum : ∀ {n} (f : Fin n → ℕ) (i : Fin n) → f i N.≤ L.sum (L.tabulate f)
          elem≤tabulate-sum f fzero    = N.m≤m+n (f fzero) _
          elem≤tabulate-sum f (fsuc i) = N.≤-trans (elem≤tabulate-sum (f ∘ fsuc) i) (N.m≤n+m _ (f fzero))

          tabulate-sum-nonZero : ∀ {n} (f : Fin n → ℕ) → ∃[ i ] NonZero (f i) → NonZero (L.sum (L.tabulate f))
          tabulate-sum-nonZero f (i , nz) =
            N.>-nonZero (N.<-≤-trans (N.>-nonZero⁻¹ (f i) ⦃ nz ⦄) (elem≤tabulate-sum f i))

    -- stake held by pools with strictly more stake than the given one
    richerStake : ℕ → ℕ
    richerStake st = L.sum (L.filter (st <?_) allStakes)
```
Voting-committee membership by stake-based truncation: order pools by
stake descending and accumulate until the cumulative stake covers the σc
target; the committee is fixed for the whole epoch. A pool with stake `st`
is on the committee iff the pools with strictly more stake do not already
cover the target. Pools of equal stake at the boundary are all included.
```agda
  inVotingCommittee : ℕ → Type
  inVotingCommittee st = (Z.+ richerStake st) Q./ totalStake Q.< σc

record TestParams (params : Params) : Type where
  open Params params

  field sutId : Fin numberOfParties
        winning-slots : ℙ ℕ
```
