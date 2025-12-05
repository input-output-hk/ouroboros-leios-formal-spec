{-# OPTIONS --safe #-}
module Prelude.Errors where

open import Prelude.Init
open import Data.String

record IsError {A : Type} (E : A → Type) : Type where
  field
    errorMsg : ∀ {x} → E x → String

open IsError ⦃...⦄ public
