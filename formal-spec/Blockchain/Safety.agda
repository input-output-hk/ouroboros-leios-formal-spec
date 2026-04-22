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

-- | Witness that an ext `Spec` extends some base honest-node spec:
-- bundles the base-side spec, the channel/layer equipment, and the block-level
-- projection.  Everything both `Safety.Transfer` and `Liveness.Transfer`
-- need; Liveness additionally takes `producer-compat`/`slotOf-compat` as
-- extra module parameters.
record IsExtension {BlockBase BlockExt : Type} {n : ℕ} {Network : Channel}
                   (ext-spec : Spec BlockExt n Network) : Type₂ where
  open Spec ext-spec using (IO; Adv)
  field
    base-IO base-Adv      : Channel
    base-honest-node-spec : Machine Network (base-IO ⊗₀ base-Adv)
    base-IsBlockchain     : IsBC.IsBlockchain (Fin n) BlockBase base-honest-node-spec
    ext-Adv≡base-Adv      : Adv ≡ base-Adv
    ext-layer             : Machine base-IO (IO ⊗₀ I)
    getBaseBlock          : BlockExt → BlockBase
    getBaseBlock-inj      : Injective _≡_ _≡_ getBaseBlock

  base-spec : Spec BlockBase n Network
  base-spec = record
    { IO                = base-IO
    ; Adv               = base-Adv
    ; honest-node-spec  = base-honest-node-spec
    ; spec-IsBlockchain = base-IsBlockchain
    }
