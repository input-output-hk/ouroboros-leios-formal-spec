{-# OPTIONS --safe #-}
open import Leios.Prelude
open import Tactic.Defaults
open import Tactic.Derive.DecEq

{- Module: Leios.Config

   This module defines the configuration parameters for the Leios protocol.
   It includes block type definitions (Input Blocks, Endorser Blocks, Votes)
   and protocol parameters such as party counts, stake distribution,
   stage length, and winning slot specifications.
-}

module Leios.Config where

data BlockType : Type where
  IB EB VT : BlockType

unquoteDecl DecEq-BlockType = derive-DecEq ((quote BlockType , DecEq-BlockType) ∷ [])

record NetworkParams : Type where
  field numberOfParties   : ℕ
        stakeDistribution : TotalMap (Fin numberOfParties) ℕ
        ⦃ NonZero-numberOfParties ⦄ : NonZero numberOfParties

record Params : Type where
  field networkParams : NetworkParams

  open NetworkParams networkParams public

record TestParams (params : Params) : Type where
  open Params params

  field sutId : Fin numberOfParties
        winning-slots : ℙ (BlockType × ℕ)
