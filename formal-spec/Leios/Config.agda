open import Leios.Prelude
open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Leios.Config where

data BlockType : Type where
  IB EB VT : BlockType

unquoteDecl DecEq-BlockType = derive-DecEq ((quote BlockType , DecEq-BlockType) ∷ [])

record NetworkParams : Type where
  field numberOfParties : ℕ
        stakeDistribution : TotalMap (Fin numberOfParties) ℕ
        stageLength : ℕ
        ⦃ NonZero-stageLength ⦄ : NonZero stageLength
        ⦃ NonZero-numberOfParties ⦄ : NonZero numberOfParties

record Params : Type where
  field networkParams : NetworkParams

  open NetworkParams networkParams public

  field sutId : Fin numberOfParties
        winning-slots : ℙ (BlockType × ℕ)
