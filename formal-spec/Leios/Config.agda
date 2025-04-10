open import Leios.Prelude

module Leios.Config where

record Params : Type where
  field numberOfParties : ℕ
        sutId : Fin numberOfParties
        stakeDistribution : TotalMap (Fin numberOfParties) ℕ
        stageLength : ℕ
        ⦃ NonZero-stageLength ⦄ : NonZero stageLength
