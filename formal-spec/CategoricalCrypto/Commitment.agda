{-# OPTIONS --safe #-}

module CategoricalCrypto.Commitment where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

data CRST : Mode → Type where
  Gen : CRST In
  Res : List Bool → CRST Out

CRS : Channel
CRS = simpleChannel CRST

module COM where

  data ComT : Mode → Type where
    Commit : Bool → ComT Out
    Open : ComT Out

  Com = simpleChannel ComT

  data VerT : Mode → Type where
    ReceiveV : VerT In
    RevealV  : Bool → VerT In

  Ver = simpleChannel VerT

  data AdvT : Mode → Type where
    ReceiveA : AdvT In
    RevealA  : Bool → AdvT In
    ReceiveReturn RevealReturn : AdvT Out

  Adv : Channel
  Adv = simpleChannel AdvT

  private variable
    b : Bool
    s : Maybe Bool

  data WithState_receive_return_newState_ : MachineType I ((Com ⊗ Ver) ⊗ Adv) (Maybe Bool) where

    Commit₁ :
      WithState nothing
      receive L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ₒ Commit b
      return just $ L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ ReceiveA
      newState just b

    Commit₂ :
      WithState s
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ ReceiveReturn
      return just $ L⊗ ((L⊗ ϵ) ⊗R) ᵗ¹ ↑ᵢ ReceiveV
      newState s

    Reveal₁ :
      WithState just b
      receive L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ₒ Open
      return just $ L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ RevealA b
      newState just b

    Reveal₂ :
      WithState just b
      receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ RevealReturn
      return just $ L⊗ ((L⊗ ϵ) ⊗R) ᵗ¹ ↑ᵢ RevealV b
      newState just b

  open Machine

  Functionality : Machine I ((Com ⊗ Ver) ⊗ Adv)
  Functionality .State   = Maybe Bool
  Functionality .stepRel = WithState_receive_return_newState_
