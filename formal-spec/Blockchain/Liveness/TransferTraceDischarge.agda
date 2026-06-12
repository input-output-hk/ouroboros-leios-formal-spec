{-# OPTIONS --safe #-}

-- ============================================================================
-- Liveness-side discharge (SKELETON).
--
-- Assembles the ext liveness (LiveHCG / Live∃CQ) from the base liveness, the
-- already-discharged `ChainLemma` (Safety/ChainLemmaDischarge), and the
-- block-level compatibilities.  Unlike the safety discharge there is one extra,
-- genuinely-new obligation — the windowing operator's naturality `recent-map`
-- — which is PROVEN here from `slot-compat` alone.  It is pure List/Block
-- combinatorics (cf. Liveness/Transfer.agda:48,91); no `≈`, no delivery.
--
-- The two compatibilities are taken as parameters; for the concrete LinearLeios
-- deployment they are `refl`, since `producer`/`slotOf` of a LeiosBlock are
-- defined as those of its `.rb`, and `getBaseBlock = .rb` (Network/Leios:124).
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (_∘ᴷ_)
import Data.List as L
import Data.Nat as N
open import Data.Bool using (true; false)

module Blockchain.Liveness.TransferTraceDischarge (n : ℕ) where

import Blockchain.Safety.TransferTrace as STT
open STT n using (Obs; mapObs; module Transfer)
import Blockchain.Liveness.TransferTrace as LTT
open LTT n using (LiveHCG; Live∃CQ; hcg-transfer; ∃cq-transfer)

-- the recent-window operator (generic over the block type and its slot)
-- cf. Blockchain/Liveness.agda:49
recent : ∀ {Block : Type} → (Block → ℕ) → ℕ → ℕ → List Block → List Block
recent slot T s = L.filter (λ b → s N.≤? (slot b N.+ T))

module _ (Reachable : ∀ {A} {Block : Type} → Machine I A → Obs Block → Type)
         {A : Channel} {BlockExt BlockBase : Type}
         {gB : BlockExt → BlockBase}
         {producerₑ : BlockExt → Fin n} {producer-b : BlockBase → Fin n}
         (honest : ℙ (Fin n))
         {slotₑ : BlockExt → ℕ} {slot-b : BlockBase → ℕ}
         (producer-compat : ∀ b → producerₑ b ≡ producer-b (gB b))
         (slot-compat     : ∀ b → slotₑ b ≡ slot-b (gB b))
         {Pₑ P-b : Machine I A}
         (chainLemma : Transfer.ChainLemma Reachable gB Pₑ P-b)   -- from ChainLemmaDischarge
  where

  -- (new obligation) naturality of the recent window under getBaseBlock,
  -- PROVEN from slot-compat.  ext/base filter decisions agree because
  -- slotₑ b ≡ slot-b (gB b); the cross cases are impossible.
  recent-map : ∀ T s (l : List BlockExt)
             → recent slot-b T s (L.map gB l) ≡ L.map gB (recent slotₑ T s l)
  recent-map T s []       = refl
  recent-map T s (b ∷ l)
    with s N.≤ᵇ (slotₑ b N.+ T)
       | s N.≤ᵇ (slot-b (gB b) N.+ T)
       | cong (λ z → s N.≤ᵇ (z N.+ T)) (slot-compat b)
  ... | true  | .true  | refl = cong (gB b L.∷_) (recent-map T s l)
  ... | false | .false | refl = recent-map T s l

  -- assembly: base liveness ⇒ ext liveness, via the stubbed transfers
  -- (`LiveHCG`/`ChainLemma` are defined functions, so the block-projection
  --  implicits must be passed by name — they appear only as `f (gB b)`.)
  live-hcg : ∀ {τ}
           → LiveHCG Reachable producer-b honest slot-b  τ P-b
           → LiveHCG Reachable producerₑ honest slotₑ τ Pₑ
  live-hcg {τ} base-live =
    hcg-transfer Reachable {gB = gB} {producerₑ = producerₑ} {producer-b = producer-b}
                    {honest = honest} {slotₑ = slotₑ} {slot-b = slot-b}
                    producer-compat slot-compat {Pₑ = Pₑ} {P-b = P-b}
                    chainLemma {τ = τ} base-live

  live-∃cq : ∀ {T}
           → Live∃CQ Reachable producer-b honest (recent slot-b) T P-b
           → Live∃CQ Reachable producerₑ honest (recent slotₑ) T Pₑ
  live-∃cq {T} base-live =
    ∃cq-transfer Reachable {gB = gB} {producerₑ = producerₑ} {producer-b = producer-b}
                    {honest = honest} {slotₑ = slotₑ} {slot-b = slot-b}
                    producer-compat slot-compat {Pₑ = Pₑ} {P-b = P-b}
                    chainLemma
                    {T = T} {recentₑ = recent slotₑ} {recent-b = recent slot-b}
                    recent-map base-live
