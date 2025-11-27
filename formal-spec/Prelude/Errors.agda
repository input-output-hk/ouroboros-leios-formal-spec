{-# OPTIONS --safe #-}
module Prelude.Errors where

open import Prelude.Init
open import Data.String
-- TODO: Use agda-pretty
-- open import Text.PrettyPrint.ANSI

record IsError {A : Type} (E : A → Type) : Type where
  field
    errorDoc : ∀ {x} → E x → String -- Doc

open IsError ⦃...⦄ public
