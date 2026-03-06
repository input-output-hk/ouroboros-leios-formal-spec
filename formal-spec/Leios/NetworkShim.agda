{-# OPTIONS --safe --no-require-unique-meta-solutions #-}
open import Leios.Prelude hiding (id; _⊗_)
open import Leios.FFD
open import Leios.SpecStructure
open import Leios.Config

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Channel.Selection

module Leios.NetworkShim (⋯ : SpecStructure)
  (let open SpecStructure ⋯)
  (params : Params)
  (let open Params params)
  (splitTxs : List Tx → List Tx × List Tx)
  (validityCheckTime : EndorserBlock → ℕ) where

open import Leios.Linear ⋯ params splitTxs validityCheckTime
open Types params hiding (Network)

record ShimState : Set where
  field iteration : ℕ
        buffer    : List (FFDA.Header ⊎ FFDA.Body)

private variable s : ShimState
                 m : FFD .Channel.outType

data NetworkT : Mode → Type where
  Activate : List (FFDA.Header ⊎ FFDA.Body) → NetworkT In
  Done     : List (FFDA.Header ⊎ FFDA.Body) → NetworkT Out

Network = simpleChannel NetworkT

messages : FFD .Channel.outType → List (FFDA.Header ⊎ FFDA.Body)
messages (FFD-IN (FFDAbstract.Send h b)) = [ inj₁ h ] ++ L.fromMaybe (inj₂ <$> b)
messages (FFD-IN FFDAbstract.Fetch)      = []

-- send SLOT 3 times
data _-⟦_/_⟧ˢ⇀_ : MachineType Network FFD ShimState where
  Begin : ∀ ms → let open ShimState s in
    ∙ iteration ≡ 0
    ──────────────────────────────────────────────────────────────────────────────────
    s -⟦ ϵ ⊗R ↑ᵢ Activate ms / just (L⊗ ϵ ↑ₒ FFD-OUT ms) ⟧ˢ⇀ record s { iteration = 1 }

  Progress : let open ShimState s in
    ∙ iteration > 0
    ∙ iteration ≤ 3
    ───────────────────────────────────────────────────────────────
    s -⟦ L⊗ ϵ ↑ᵢ m / just (L⊗ ϵ ↑ₒ SLOT) ⟧ˢ⇀ record
      { iteration = suc iteration ; buffer = buffer ++ messages m }

  Finish : let open ShimState s in
    ∙ iteration ≡ 4
    ─────────────────────────────────────────────────────────────────────
    s -⟦ L⊗ ϵ ↑ᵢ m / just (ϵ ⊗R ↑ₒ Done (buffer ++ messages m)) ⟧ˢ⇀ record
      { iteration = 0 ; buffer = [] }


Shim : Machine Network FFD
Shim .Machine.State = ShimState
Shim .Machine.stepRel = _-⟦_/_⟧ˢ⇀_
