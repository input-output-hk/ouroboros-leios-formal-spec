{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)

open import CategoricalCrypto hiding (id; _∘_)
open import CategoricalCrypto.Machine.Iso using (_≅ᴹ_)

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
    -- The channel of an honest node, component by component.  These are not
    -- consequences of `honest-nodes-≡-spec`: that equates the tensors
    -- `IOF p ⊗₀ AdvF p` and `IO ⊗₀ Adv`, and `_⊗₀_` — a sum of types — is not
    -- injective, so the factors have to be given.  For a uniform deployment
    -- (`IOF = const IO`, `AdvF = const Adv`) both are `λ _ → refl`.
    honest-IOF          : ∀ {p} → p ∈ honest-nodes → IOF p ≡ IO
    honest-AdvF         : ∀ {p} → p ∈ honest-nodes → AdvF p ≡ Adv
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

-- | Witness that one `Spec` extends a given base `Spec`: the ext honest node
-- is an extension layer stacked (`_∘ᴷ_`) on the base honest node.  The layer
-- has its own adversary channel `AdvL`, so the ext adversary channel is the
-- base one next to the layer's.
--
-- The correspondence is a machine isomorphism (`_≅ᴹ_`), not propositional
-- equality: the two sides are built from different combinators and have
-- different `State` types, so `_≡_` between them is not provable, whereas
-- the transfer proofs only ever use the iso.
record IsExtension {BlockBase BlockExt : Type} {n : ℕ} {Network : Channel}
                   (base-spec : Spec BlockBase n Network)
                   (ext-spec  : Spec BlockExt  n Network) : Type₂ where
  private
    module B = Spec base-spec
    module E = Spec ext-spec
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
