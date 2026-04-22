{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)

open import CategoricalCrypto hiding (id; _∘_)

import Blockchain.IsBlockchain as IsBC

module Blockchain.Safety where

-- | The single-node blockchain spec: one machine that answers blockchain
-- queries, plus its `IsBlockchain` evidence.
record Spec (Block : Type) (n : ℕ) (Network : Channel) : Type₂ where
  field
    IO Adv            : Channel
    honest-node-spec  : Machine Network (IO ⊗₀ Adv)
    spec-IsBlockchain : IsBC.IsBlockchain (Fin n) Block honest-node-spec
  open IsBC.IsBlockchain spec-IsBlockchain public using (producer; slotOf)

-- | Deployment of a spec across `n` nodes.  Depends on `Spec` only
-- via `honest-node-spec` (used in `honest-nodes-≡-spec`).
record Deployment {Block : Type} {n : ℕ} {Network : Channel}
                        (spec : Spec Block n Network) : Type₂ where
  open Spec spec
  open IsBC (Fin n)
  field
    NAdv                : Channel
    IOF AdvF            : Fin n → Channel
    all-nodes           : (p : Fin n) → Machine Network (IOF p ⊗₀ AdvF p)
    honest-nodes        : ℙ (Fin n)
    honest-nodes-≡-spec : ∀ {p} → p ∈ honest-nodes → all-nodes p ≡ᴹ honest-node-spec
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

  safeState : {A : Channel} → ℕ → (E : Environment A) → Machine.State (protocol E) → Type
  safeState k E S =
    {p p'       : Fin n}
    (honest-p   : p  ∈ honest-nodes)
    (honest-p'  : p' ∈ honest-nodes)
    → prune k (getChain E S honest-p) ≼ getChain E S honest-p'

  safety : ℕ → Type₁
  safety k = ∀ {A} (E : Environment A) → Invariant (protocol E) (safeState k E)

-- | Combined single-/multi-node record; kept as the user-facing API.  The
-- public re-opens below make every old `Safety.X` projection resolve.
record Safety (Block : Type) : Type₂ where
  field
    n          : ℕ
    Network    : Channel
    spec       : Spec Block n Network
    deployment : Deployment spec
  open Spec spec public
  open Deployment deployment public

-- | Witness that an ext `Spec` extends a given base `Spec`: bundles the
-- channel/layer equipment and the block-level projection.  Everything both
-- `Safety.Transfer` and `Liveness.Transfer` need; Liveness additionally takes
-- `producer-compat`/`slotOf-compat` as extra module parameters.
record IsExtension {BlockBase BlockExt : Type} {n : ℕ} {Network : Channel}
                   (base-spec : Spec BlockBase n Network)
                   (ext-spec  : Spec BlockExt  n Network) : Type₂ where
  private
    module B = Spec base-spec
    module E = Spec ext-spec
  field
    ext-Adv≡base-Adv : E.Adv ≡ B.Adv
    ext-layer        : Machine B.IO (E.IO ⊗₀ I)
    -- The ext honest-node spec factors through the base honest-node spec via
    -- `ext-layer`, modulo the `Adv`-channel equality.  This is the equational
    -- core of "ext extends base" and lets `Safety.Transfer` derive
    -- `single-protocol-≡` from this record rather than asking for it.
    is-extension : idᴷ ∘ᴷ E.honest-node-spec
                 ≡ subst (λ A → Machine Network (E.IO ⊗₀ (A ⊗₀ I)))
                         (sym ext-Adv≡base-Adv)
                         (ext-layer ∘ᴷ B.honest-node-spec)
    getBaseBlock     : BlockExt → BlockBase
    getBaseBlock-inj : Injective _≡_ _≡_ getBaseBlock
