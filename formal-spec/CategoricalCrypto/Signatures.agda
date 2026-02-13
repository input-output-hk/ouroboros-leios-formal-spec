{-# OPTIONS --safe #-}
module CategoricalCrypto.Signatures where

open import abstract-set-theory.Prelude hiding (id; _∘_; _⊗_; lookup; Dec)
import abstract-set-theory.Prelude as P

open import Data.Fin using (Fin; fromℕ<) renaming (zero to fzero; suc to fsuc)

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core

open import Data.Nat
open import Data.List
open import Data.List.Membership.Propositional

open import Function

module Signatures (VK M S : Set) where
  data SigT : Mode → Type where
    Gen : SigT Out
    GetPk : VK → SigT In
    Sign : M → SigT Out
    GetSig : S → SigT In

  Sig : Channel
  Sig = simpleChannel SigT

  data VerT : Mode → Type where
    Verify : VK → M → S → VerT Out

  Ver : Channel
  Ver = simpleChannel VerT

  data AdvT : Mode → Type where
    GenA : AdvT In
    GenPk : VK → AdvT Out
    SignA : M → ℕ → AdvT In
    SignSig : S → ℕ → AdvT Out

  Adv : Channel
  Adv = simpleChannel AdvT

  record State : Set where
    field key : Maybe VK
          verList : List (VK × M × S)
          msgs : List M
          seenIds : List ℕ

  data WithState_receive_return_newState_ : MachineType I ((Sig ⊗ Ver) ⊗ Adv) State where

    Gen₁NI : ∀ {s}
           → State.key s ≡ nothing
           → WithState s
             receive L⊗ ((ϵ ⊗R) ⊗R) ᵗ² ↑ₒ Gen
             return just $ L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ GenA
             newState s

    Gen₂NI : ∀ {s vk}
           → State.key s ≡ nothing
           → WithState s
             receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ GenPk vk
             return just $ L⊗ ((ϵ ⊗R) ⊗R) ᵗ¹ ↑ᵢ GetPk vk
             newState record s { key = just vk }

    GenI : ∀ {s vk}
         → State.key s ≡ just vk
         → WithState s
           receive L⊗ ((ϵ ⊗R) ⊗R) ᵗ² ↑ₒ Gen 
           return just $ L⊗ ((ϵ ⊗R) ⊗R) ᵗ² ↑ᵢ GetPk vk
           newState s

    Sign₁ : ∀ {s vk m}
          → let open State s in
            State.key s ≡ just vk
          → WithState s
            receive L⊗ ((ϵ ⊗R) ⊗R) ᵗ² ↑ₒ Sign m
            return just $ L⊗ (L⊗ ϵ) ᵗ¹ ↑ᵢ SignA m (length msgs)
            newState record s { msgs = m ∷ State.msgs s }

    Sign₂ : ∀ {s vk σ k m}
          → let open State s in
            State.key s ≡ just vk
          → k ∉ seenIds
          → (k<len : k < length msgs)
          → P.lookup msgs (fromℕ< k<len) ≡ m
          → WithState s
            receive L⊗ (L⊗ ϵ) ᵗ¹ ↑ₒ SignSig σ k
            return just $ L⊗ ((ϵ ⊗R) ⊗R) ᵗ² ↑ᵢ GetSig σ
            newState record s { verList = (vk , m , σ) ∷ State.verList s ; seenIds = k ∷ seenIds }

    -- TODO
    -- Ver : ∀ {s vk σ k m}
    --       → let open State s in
    --         WithState s
    --         receive adversarialInput (-, SignSig σ k)
    --         return just $ honestOutputO (rcvˡ (-, GetSig σ))
    --         newState record s { verList = (vk , m , σ) ∷ State.verList s ; seenIds = k ∷ seenIds }

  _-⟦_/_⟧⇀_ = WithState_receive_return_newState_

  Functionality : Machine I ((Sig ⊗ Ver) ⊗ Adv)
  Functionality .Machine.State   = State
  Functionality .Machine.stepRel = WithState_receive_return_newState_

  opaque
    unfolding
      _⊗_

    signTwice : ∀ {s s' m o}
      → s  -⟦ L⊗ ((ϵ ⊗R) ⊗R) ᵗ² ↑ₒ Sign m / o  ⟧⇀ s' → ∃[ o' ] ∃[ s'' ]
        s' -⟦ L⊗ ((ϵ ⊗R) ⊗R) ᵗ² ↑ₒ Sign m / o' ⟧⇀ s''
    signTwice (Sign₁ s-key≡just-vk) = -, -, Sign₁ s-key≡just-vk
