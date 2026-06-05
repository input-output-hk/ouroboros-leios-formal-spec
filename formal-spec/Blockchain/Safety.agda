{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)

open import CategoricalCrypto hiding (id; _∘_)

import Blockchain.IsBlockchain as IsBC

module Blockchain.Safety where

-- | A specification for a blockchain
record Spec (Block : Type) (n : ℕ) (Network : Channel) : Type₂ where
  field
    IO Adv            : Channel
    honest-node-spec  : Machine Network (IO ⊗₀ Adv)
    spec-IsBlockchain : IsBC.IsBlockchain (Fin n) Block honest-node-spec
  open IsBC.IsBlockchain spec-IsBlockchain public using (producer; slotOf)

-- | Deployment of a spec across `n` nodes. Honest nodes must behave
-- according to `spec`, others can be completely arbitrary.
record Deployment (Block : Type) : Type₂ where
  field
    n       : ℕ
    Network : Channel
    spec    : Spec Block n Network
  open Spec spec public
  open IsBC (Fin n) public
  field
    NAdv                : Channel
    IOF AdvF            : Fin n → Channel
    all-nodes           : (p : Fin n) → Machine Network (IOF p ⊗₀ AdvF p)
    honest-nodes        : ℙ (Fin n)
    honest-nodes-≡-spec : ∀ {p} → p ∈ honest-nodes → all-nodes p ≡ᴹ honest-node-spec
    -- honest parties carry the spec's I/O and adversary channels (supplied
    -- directly, so consumers need not decompose `honest-nodes-≡-spec`'s
    -- codomain equality via channel injectivity)
    honest-IOF≡         : ∀ {p} → p ∈ honest-nodes → IOF p ≡ IO
    honest-AdvF≡        : ∀ {p} → p ∈ honest-nodes → AdvF p ≡ Adv
    network             : Machine I (n ⨂ⁿ Network ⊗₀ NAdv)

  honest-nodes-blockchain : ∀ {p} → p ∈ honest-nodes → IsBlockchain Block (all-nodes p)
  honest-nodes-blockchain p-honest =
    ≡ᴹ-subst (IsBlockchain Block) (≡ᴹ-sym (honest-nodes-≡-spec p-honest)) spec-IsBlockchain

  nodes : Machine (n ⨂ⁿ Network) (⨂ IOF ⊗₀ ⨂ AdvF)
  nodes = ⨂ᴷ all-nodes

  Environment : Channel → Type₁
  Environment A = Machine (⨂ IOF ⊗₀ (NAdv ⊗₀ ⨂ AdvF)) A

  protocol : ∀ {A} → Environment A → Machine I A
  protocol E = E CategoricalCrypto.∘ (nodes ∘ᴷ network)

  query : (bci : BlockChainInfo Block)
          {p : Fin n} {A : Channel}
          (E : Environment A)
          → Machine.State (protocol E)
          → p ∈ honest-nodes
          → bciQueryType bci
  query bci {p} _ (((_ , s , tt) , tt) , _) honest-p = proj₁ (queryCompute bci (⨂ᴷ-sub-state p s))
    where
      module IB = IsBlockchain (honest-nodes-blockchain honest-p)
      open IsConstrained IB.isConstrained

  getChain = query Chain
  getSlot  = query Slot

  -- NOTE: the state-`Invariant` formulation of safety (`safeState`/`safety`)
  -- has been retired in favour of the observation-based `Safe` of the
  -- trace-equivalence rework (`Blockchain.Safety.TransferTrace`).

-- | Witness that one `Spec` extends a given base `Spec`: see the reworked
-- `Blockchain.Safety.TransferTrace.Transfer.IsExtension≈` (trace-equivalence,
-- with a Machine iso `adv-iso` in place of the propositional `E.Adv ≡ B.Adv`).
-- The legacy `≡ᴹ`-based `IsExtension` record was retired with this rework.
