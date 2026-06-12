{-# OPTIONS --safe #-}

-- ============================================================================
-- Trace-equivalence rework of `Blockchain/Liveness/Transfer.agda` (SKELETON).
--
-- Mirrors Blockchain/Safety/TransferTrace.agda: properties move from
-- `Machine.State` to OBSERVATIONS (`Obs`), and the same `ChainLemma`
-- (`Pₑ ≈ P-b`  ×  observation projection along `getBaseBlock`) is reused.
--
-- Two simplifications the trace framing buys, vs the original:
--   * SlotLemma is absorbed: `mapObs` preserves `clockOf` (the party's current
--     slot) by construction, so no separate `SlotLemma`/`slotOf-compat`
--     obligation for the clock.
--   * Single direction: the original transports the predicate at both the
--     initial and final state (`hcgState-ext⇒base` AND `…-base⇒ext`); here a
--     property is `∀ reachable obs → P obs`, so only the base⇒ext conversion of
--     the predicate is needed.  `≈` itself is used only to DISCHARGE ChainLemma
--     (via `≈-Reachable`), never in these transfers — same as safety.
--
-- HCG transfer is PROVEN (map-++/length-map).  ∃CQ transfer is proven from the
-- windowing operator and its projection lemma `recent-map`, which are taken as
-- parameters here: they are pure List/Block combinatorics that carry over
-- verbatim from `Liveness/Transfer.agda:48,91` (filter-map/filter-≐), with no
-- categorical content.
-- ============================================================================

open import Leios.Prelude hiding (id; _⊗_; _∘_)
open import CategoricalCrypto hiding (_∘ᴷ_)

import Data.Integer as ℤ
import Data.Rational as ℚ
open ℚ using (ℚ)
import Data.List as L
open import Data.List.Properties using (map-++; length-map)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as AnyP

module Blockchain.Liveness.TransferTrace (n : ℕ) where

-- reuse Obs / mapObs / Transfer from the safety rework
import Blockchain.Safety.TransferTrace as STT
open STT n using (Obs; mapObs; module Transfer)
open Obs

ℕ→ℚ : ℕ → ℚ
ℕ→ℚ k = (ℤ.+ k) ℚ./ 1

module _ (Reachable : ∀ {A} {Block : Type} → Machine I A → Obs Block → Type) where
  open Transfer Reachable using (ChainLemma)  -- same ChainLemma as safety

  -- shared shape of the two block-level liveness predicates, generic over the
  -- block type and its producer/slot projections (cf. Liveness.agda:32,52)
  module _ {Block : Type} (producer : Block → Fin n) (honest : ℙ (Fin n)) where

    isHonest : Block → Type
    isHonest b = producer b ∈ honest

    -- (HCG) honest chain growth, as a predicate on an observation
    hcgPred : (slot : Block → ℕ) → ℚ → Obs Block → Type
    hcgPred slot τ o =
        (p : Fin n) {pref suff : List Block} {b : Block}
      → chainOf o p ≡ pref ++ b ∷ suff
      → isHonest b
      → τ ℚ.* ℕ→ℚ (clockOf o p ∸ slot b) ℚ.≤ ℕ→ℚ (length suff)

    -- (∃CQ) existential chain quality, parametric in the recent-window operator
    ∃cqPred : (recent : ℕ → ℕ → List Block → List Block) → ℕ → Obs Block → Type
    ∃cqPred recent T o =
        (p : Fin n) → Any.Any isHonest (recent T (clockOf o p) (chainOf o p))

  -- protocol-level liveness over reachable observations
  -- (was: `hcg τ`/`∃cq T` as `Invariant`s, Liveness.agda:40,57)
  LiveHCG : ∀ {A} {Block} (producer : Block → Fin n) (honest : ℙ (Fin n))
            (slot : Block → ℕ) → ℚ → Machine I A → Type
  LiveHCG producer honest slot τ P =
    ∀ {o} → Reachable P o → hcgPred producer honest slot τ o

  Live∃CQ : ∀ {A} {Block} (producer : Block → Fin n) (honest : ℙ (Fin n))
            (recent : ℕ → ℕ → List Block → List Block) → ℕ → Machine I A → Type
  Live∃CQ producer honest recent T P =
    ∀ {o} → Reachable P o → ∃cqPred producer honest recent T o

  -- --------------------------------------------------------------------------
  -- The transfers.  Compatibility hypotheses match the original
  -- producer-compat / slot-compat (Liveness/Transfer.agda:32-35).
  -- --------------------------------------------------------------------------
  module _ {BlockExt BlockBase : Type}
           {gB : BlockExt → BlockBase}
           {producerₑ : BlockExt → Fin n} {producer-b : BlockBase → Fin n}
           {honest : ℙ (Fin n)}
           {slotₑ : BlockExt → ℕ} {slot-b : BlockBase → ℕ}
           (producer-compat : ∀ b → producerₑ b ≡ producer-b (gB b))
           (slot-compat     : ∀ b → slotₑ b ≡ slot-b (gB b))
           {A} {Pₑ P-b : Machine I A}
           (chainLemma : ChainLemma gB Pₑ P-b)
    where

    private proj = proj₂ chainLemma

    -- HCG: base ⇒ ext.  Map the ext split forward to a base split.
    hcg-transfer : ∀ {τ}
                 → LiveHCG producer-b honest slot-b τ P-b
                 → LiveHCG producerₑ honest slotₑ τ Pₑ
    hcg-transfer {τ} base-live {o} reach p {pref} {suff} {b} eq hb =
      subst₂ (λ s ℓ → τ ℚ.* ℕ→ℚ (clockOf o p ∸ s) ℚ.≤ ℕ→ℚ ℓ)
             (sym (slot-compat b)) (length-map gB suff)
             (base-live (proj reach) p
               (trans (cong (L.map gB) eq) (map-++ gB pref (b ∷ suff)))
               (subst (_∈ honest) (producer-compat b) hb))

    -- ∃CQ: base ⇒ ext.  Pull the base witness back through `recent-map`.
    ∃cq-transfer : ∀ {T}
                   {recentₑ : ℕ → ℕ → List BlockExt  → List BlockExt}
                   {recent-b : ℕ → ℕ → List BlockBase → List BlockBase}
                 → (recent-map : ∀ T s l
                     → recent-b T s (L.map gB l) ≡ L.map gB (recentₑ T s l))
                 → Live∃CQ producer-b honest recent-b T P-b
                 → Live∃CQ producerₑ honest recentₑ T Pₑ
    ∃cq-transfer {T} recent-map base-live {o} reach p =
      Any.map (λ {b} h → subst (_∈ honest) (sym (producer-compat b)) h)
        (AnyP.map⁻
          (subst (Any.Any (λ b' → producer-b b' ∈ honest))
                 (recent-map T (clockOf o p) (chainOf o p))
                 (base-live (proj reach) p)))
