{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)

open import CategoricalCrypto hiding (id; _∘_)

open import Blockchain.Safety using (Deployment)

import Data.Integer as ℤ
import Data.Rational as ℚ
open ℚ using (ℚ)

module Blockchain.Liveness
  (Block : Type)
  (S     : Deployment Block)
  where

open Deployment S

ℕ→ℚ : ℕ → ℚ
ℕ→ℚ n = (ℤ.+ n) ℚ./ 1

isHonestBlock : Block → Type
isHonestBlock b = producer b ∈ honest-nodes

-- --------------------------------------------------------------------
-- (HCG) Honest Chain Growth
--
-- For every honest block `b` in an honest party's chain, the number
-- of blocks that follow `b` is at least τ · (currentSlot ∸ slotOf b).

-- NOTE: the state-`Invariant` formulation (`hcgState`/`hcg`, `∃cqState`/`∃cq`)
-- has been retired in favour of the observation-based `LiveHCG`/`Live∃CQ` of the
-- trace-equivalence rework (`Blockchain.Liveness.TransferTrace`).

-- --------------------------------------------------------------------
-- (∃CQ) Existential Chain Quality
--
-- In every honest party's chain, the suffix of blocks whose slot is
-- within the last T slots contains at least one honest block.

recent : ℕ → ℕ → List Block → List Block
recent T s = filter (λ b → slotOf b + T ≥ s)
