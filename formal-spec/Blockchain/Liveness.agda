{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)

open import CategoricalCrypto hiding (id; _∘_)

open import Blockchain.Safety using (Safety)

import Data.Integer as ℤ
import Data.Rational as ℚ
open ℚ using (ℚ)

module Blockchain.Liveness
  (Block : Type)
  (S     : Safety Block)
  where

open Safety S

private
  ℕ→ℚ : ℕ → ℚ
  ℕ→ℚ n = (ℤ.+ n) ℚ./ 1

-- Additional structure needed for liveness: every block has a producer
-- (a party) and a slot number. A block is honest iff its producer is
-- an honest party.
record Liveness : Type where
  field
    producer : Block → Fin n
    slotOf   : Block → ℕ

  isHonestBlock : Block → Type
  isHonestBlock b = producer b ∈ honest-nodes

  -- --------------------------------------------------------------------
  -- (HCG) Honest Chain Growth
  --
  -- For every honest block `b` in an honest party's chain, the number
  -- of blocks that follow `b` is at least τ · (currentSlot ∸ slotOf b).
  -- The genesis block (assumed honest) makes this imply a bound on
  -- absolute chain length vs. current slot.

  hcgState : {A : Channel} → ℚ → (E : Environment A) → Machine.State (protocol E) → Type
  hcgState τ E S₀ =
      {p : Fin n} (hp : p ∈ honest-nodes)
      {pref suff : List Block} {b : Block}
    → getChain E S₀ hp ≡ pref ++ (b ∷ suff)
    → isHonestBlock b
    → τ ℚ.* ℕ→ℚ (getSlot E S₀ hp ∸ slotOf b) ℚ.≤ ℕ→ℚ (length suff)

  hcg : ℚ → Type₁
  hcg τ = ∀ {A} (E : Environment A) → Invariant (protocol E) (hcgState τ E)

  -- --------------------------------------------------------------------
  -- (∃CQ) Existential Chain Quality
  --
  -- In every honest party's chain, the suffix of blocks whose slot is
  -- within the last T slots contains at least one honest block. The
  -- assumed honest genesis block guarantees this list is non-empty
  -- during startup.

  recent : ℕ → ℕ → List Block → List Block
  recent T s = filter (λ b → slotOf b + T ≥ s)

  ∃cqState : {A : Channel} → ℕ → (E : Environment A) → Machine.State (protocol E) → Type
  ∃cqState T E S₀ =
      {p : Fin n} (hp : p ∈ honest-nodes)
    → Any.Any isHonestBlock (recent T (getSlot E S₀ hp) (getChain E S₀ hp))

  ∃cq : ℕ → Type₁
  ∃cq T = ∀ {A} (E : Environment A) → Invariant (protocol E) (∃cqState T E)
