{-# OPTIONS --safe #-}

-- ============================================================================
-- Discharging `ChainLemma` for the concrete deployment (SKELETON).
-- This is the one place `≈-Reachable` is finally CONSUMED.
--
--   ChainLemma gB Pₑ P-b
--     = (Pₑ ≈ P-b)
--     × (∀ {o} → Reachable Pₑ o → Reachable P-b (mapObs gB o))
--
-- with Pₑ = Ext.protocol E  (LinearLeios, closed)  and
--      P-b = Base.protocol (transEnv E)  (derived Praos, closed).
--
-- It rests on exactly two deployment-specific obligations:
--
--   (I)  ≈-protocol : Pₑ ≈ P-b
--        The trace-equivalence analogue of `transProtocol`
--        (Safety/Transfer.agda:105).  Built from `IsExtension≈.is-extension`
--        (per honest node, now stated at ≈) lifted over ⨂ and composed with
--        the environment + network, using the congruences `∘-resp-≈` /
--        `⊗₁-resp-≈` and the structural-iso ≈-laws.  See the derivation sketch
--        at the bottom — its sub-steps are the ≈-analogues of
--        `single-protocol-≡`, `insert-id`, `⨂-absorb-env`.
--
--   (II) reindex
--        Reading a reachable trace point of the base (Praos) machine via the
--        BASE IsBlockchain query yields the getBaseBlock-projection of reading
--        it via the EXT IsBlockchain query.  This is the genuine "RB backbone
--        = projection" content (the two `queryCompute`s related by
--        getBaseBlock); cf. the original `ChainLemma-ty`, Safety/Transfer:125.
--
-- Given those, `≈-Reachable` does the single remaining job: carry a reachable
-- observation across the machine isomorphism.  Everything categorical is a
-- library fact; everything protocol-specific is (I) and (II); the observation
-- semantics (`Reachable`/`≈-Reachable`) are the open parameters.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (_∘ᴷ_)
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_)

module Blockchain.Safety.ChainLemmaDischarge (n : ℕ) where

import Blockchain.Safety.TransferTrace as STT
open STT n using (Obs; mapObs; module Transfer)

module _
  (Reachable   : ∀ {A} {Block : Type} → Machine I A → Obs Block → Type)
  (≈-Reachable : ∀ {A} {Block} {P Q : Machine I A} → P ≅ᴹ Q
               → ∀ {o : Obs Block} → Reachable P o → Reachable Q o)
  where
  open Transfer Reachable using (ChainLemma)

  module _ {A : Channel} {BlockExt BlockBase : Type}
           (gB : BlockExt → BlockBase)
           {Pₑ P-b : Machine I A}
           (≈-protocol : Pₑ ≅ᴹ P-b)                             -- (I)
           (reindex    : ∀ {o : Obs BlockExt}
                       → Reachable P-b o → Reachable P-b (mapObs gB o))  -- (II)
    where

    -- The actual discharge.  `≈-Reachable` is used exactly once.
    chainLemma : ChainLemma gB Pₑ P-b
    chainLemma = ≈-protocol , λ reach → reindex (≈-Reachable ≈-protocol reach)

-- ============================================================================
-- Derivation sketch for obligation (I), ≈-protocol — NOT mechanised here,
-- since the ⨂/network congruences it needs are packaged as `env-absorb`
-- in this skeleton.  It is the ≈-analogue of `transProtocol`:
--
--   Ext.protocol E
--     = E ∘ (Ext.nodes ∘ᴷ Ext.network)
--     ≈⟨ ⨂-congruence on the per-node `is-extension≈`           ⟩  -- ≈ of `single-protocol-≡`
--       E ∘ (⨂ (λ p → extPart p ∘ base-node p) ∘ᴷ network)
--     ≈⟨ ⨂-absorb-env / insert-id, packaged as `env-absorb`      ⟩
--       (E ∘ structure-isos ∘ ⨂ extPart) ∘ (Base.nodes ∘ᴷ network)
--     = Base.protocol (transEnv E)
--
-- The per-node input is precisely `IsExtension≈.is-extension`
-- (TransferTrace.agda):  honest-node ≈ (ext-layer ⊗₁ adv-iso.from) ∘ base-node.
-- Lifting it needs only `∘-resp-≈`, `⊗₁-resp-≈` and the monoidal ≈-coherence —
-- all theorems of the explicit Machine category, none about delivery.
-- ============================================================================
