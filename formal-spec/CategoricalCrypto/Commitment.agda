{-# OPTIONS --safe #-}
module CategoricalCrypto.Commitment where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)
import abstract-set-theory.Prelude as P

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import CategoricalCrypto.Base

data CRST : ChannelDir → Type where
  Gen : CRST In
  Res : List Bool → CRST Out

CRS : Channel
CRS = simpleChannel' CRST

module COM where

  data ComT : ChannelDir → Type where
    Commit : Bool → ComT Out
    Open : ComT Out

  Com = simpleChannel' ComT

  data VerT : ChannelDir → Type where
    ReceiveV : VerT In
    RevealV  : Bool → VerT In

  Ver = simpleChannel' VerT

  data AdvT : ChannelDir → Type where
    ReceiveA : AdvT In
    RevealA  : Bool → AdvT In
    ReceiveReturn RevealReturn : AdvT Out

  Adv : Channel
  Adv = simpleChannel' AdvT

  private variable
    b : Bool
    s : Maybe Bool

  data WithState_receive_return_newState_ : MachineType I ((Com ⊗ Ver) ⊗ Adv) (Maybe Bool) where

    Commit₁ :
      WithState nothing
      receive honestInputI (sndˡ (-, Commit b))
      return just $ adversarialOutput (-, ReceiveA)
      newState just b

    Commit₂ :
      WithState s
      receive adversarialInput (-, ReceiveReturn)
      return just (honestOutputO (rcvʳ (-, ReceiveV)))
      newState s

    Reveal₁ :
      WithState just b
      receive honestInputI (sndˡ (-, Open))
      return just $ adversarialOutput (-, RevealA b)
      newState just b

    Reveal₂ :
      WithState just b
      receive adversarialInput (-, RevealReturn)
      return just (honestOutputO (rcvʳ (-, RevealV b)))
      newState just b

  open Machine

  Functionality : Machine I ((Com ⊗ Ver) ⊗ Adv)
  Functionality .State   = Maybe Bool
  Functionality .stepRel = WithState_receive_return_newState_
