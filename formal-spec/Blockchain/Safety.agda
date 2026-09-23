{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_)

import Blockchain.IsBlockchain as IsBC
open import CategoricalCrypto.Ext using (subst-≡ᴹ-out)

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
  open IsBC public
  field
    NAdv                : Channel
    IOF AdvF            : Fin n → Channel
    all-nodes           : (p : Fin n) → Machine Network (IOF p ⊗₀ AdvF p)
    honest-nodes        : ℙ (Fin n)
    honest-nodes-≡-spec : ∀ {p} → p ∈ honest-nodes → all-nodes p ≡ᴹ honest-node-spec
    honest-IOF          : ∀ {p} → p ∈ honest-nodes → IOF p ≡ IO
    honest-AdvF         : ∀ {p} → p ∈ honest-nodes → AdvF p ≡ Adv
    network             : Machine I (n ⨂ⁿ Network ⊗₀ NAdv)

  honest-nodes-blockchain : ∀ {p} → p ∈ honest-nodes → IsBlockchain (Fin n) Block (all-nodes p)
  honest-nodes-blockchain p-honest =
    ≡ᴹ-subst (IsBlockchain (Fin n) Block) (≡ᴹ-sym (honest-nodes-≡-spec p-honest)) spec-IsBlockchain

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

-- Observation helpers for an extension, defined outside `IsExtension` so that
-- they may be used in the type of its last field.
module ExtObs {BlockBase BlockExt : Type} {n : ℕ} {Network : Channel}
              (base-spec : Spec BlockBase n Network)
              (ext-spec  : Spec BlockExt  n Network) where
  private
    module B = Spec base-spec
    module E = Spec ext-spec

  -- The base node's state inside an ext node's: what the extension
  -- isomorphism exposes, once the layer's own state is dropped.
  baseState : (AdvL : Channel) (layer : Machine B.IO (E.IO ⊗₀ AdvL))
              (eq : E.Adv ≡ B.Adv ⊗₀ AdvL)
            → E.honest-node-spec ≅ᴹ subst (λ A → Machine Network (E.IO ⊗₀ A))
                                          (sym eq) (layer ∘ᴷ B.honest-node-spec)
            → Machine.State E.honest-node-spec → Machine.State B.honest-node-spec
  baseState AdvL layer eq iso σ =
    proj₁ (proj₁ (state-subst (subst-≡ᴹ-out (sym eq) (layer ∘ᴷ B.honest-node-spec))
                              (_≅ᴹ_.to iso σ)))

  extAns : (bci : IsBC.BlockChainInfo BlockExt)
         → Machine.State E.honest-node-spec → IsBC.bciQueryType bci
  extAns bci σ = proj₁ (IsConstrained.queryCompute
    (IsBC.IsBlockchain.isConstrained E.spec-IsBlockchain) bci σ)

  baseAns : (bci : IsBC.BlockChainInfo BlockBase)
          → Machine.State B.honest-node-spec → IsBC.bciQueryType bci
  baseAns bci σ = proj₁ (IsConstrained.queryCompute
    (IsBC.IsBlockchain.isConstrained B.spec-IsBlockchain) bci σ)

-- | Witness that one `Spec` extends a given base `Spec`.
-- The layer has its own adversary channel `AdvL`.
record IsExtension {BlockBase BlockExt : Type} {n : ℕ} {Network : Channel}
                   (base-spec : Spec BlockBase n Network)
                   (ext-spec  : Spec BlockExt  n Network) : Type₂ where
  private
    module B = Spec base-spec
    module E = Spec ext-spec
    module O = ExtObs base-spec ext-spec
  field
    AdvL             : Channel
    ext-layer        : Machine B.IO (E.IO ⊗₀ AdvL)
    getBaseBlock     : BlockExt → BlockBase

    ext-Adv≡base-Adv⊗AdvL : E.Adv ≡ B.Adv ⊗₀ AdvL
    getBaseBlock-inj : Injective _≡_ _≡_ getBaseBlock
    is-extension : E.honest-node-spec
                 ≅ᴹ subst (λ A → Machine Network (E.IO ⊗₀ A))
                          (sym ext-Adv≡base-Adv⊗AdvL)
                          (ext-layer ∘ᴷ B.honest-node-spec)

    -- Observations are preserved: asking the ext node is asking the base node
    -- it is stacked on.  This is what makes the chain and slot lemmas true,
    -- and it is genuinely extra data — `is-extension` relates the two nodes as
    -- MACHINES and says nothing about their `IsBlockchain` structures, which a
    -- machine does not determine (see `Blockchain.QueryChoice`).
    query-compat : ∀ bci σ
      → IsBC.mapAnswer getBaseBlock bci (O.extAns bci σ)
      ≡ O.baseAns (IsBC.baseQ bci)
          (O.baseState AdvL ext-layer ext-Adv≡base-Adv⊗AdvL is-extension σ)

  baseStateOf : Machine.State E.honest-node-spec → Machine.State B.honest-node-spec
  baseStateOf = O.baseState AdvL ext-layer ext-Adv≡base-Adv⊗AdvL is-extension

  mapAnswer : (bci : IsBC.BlockChainInfo BlockExt)
            → IsBC.bciQueryType bci → IsBC.bciQueryType (IsBC.baseQ {Block₂ = BlockBase} bci)
  mapAnswer = IsBC.mapAnswer getBaseBlock
