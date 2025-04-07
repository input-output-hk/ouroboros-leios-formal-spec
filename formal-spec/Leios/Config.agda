open import Leios.Prelude

module Leios.Config where

record Params : Type where
  field numberOfParties : ℕ
        SUT-id : Fin numberOfParties
        sd : TotalMap (Fin numberOfParties) ℕ
