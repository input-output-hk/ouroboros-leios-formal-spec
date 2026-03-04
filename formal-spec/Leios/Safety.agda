{-# OPTIONS --safe #-}

open import Leios.Config
open import Leios.Prelude hiding (id; _⊗_)

open import CategoricalCrypto hiding (id; _∘_)

module Leios.Safety (Block : Type) where

-- | Type of things we can query from a honest node
data BlockChainInfo : Type where
  Chain : BlockChainInfo

-- | Type for responses given a specific query
bciQueryType : BlockChainInfo → Type
bciQueryType Chain = List Block

record IsBlockchain {A B : Channel} (m : Machine A B) : Type₂ where
  field 
    isConstrained : IsConstrained m bciQueryType
    isPure        : IsPure isConstrained 

record Safety : Type₂ where
  field
    -- Number of involved nodes
    n                        : ℕ
    -- Communication channels involved in the network
    IO Adv NAdv Network      : Channel
    -- Machine describing the behavior of the honest nodes
    honest-node-spec         : Machine Network (IO ⊗ Adv)
    -- The spec can be queried in the right ways
    spec-IsBlockchain        : IsBlockchain honest-node-spec
    -- Channels for all nodes
    IOF AdvF                 : Fin n → Channel
    -- All the nodes, including honest nodes and adversaries
    all-nodes                : (p : Fin n) → Machine Network (IOF p ⊗ AdvF p)
    -- All the honest nodes
    honest-nodes             : ℙ (Fin n) -- Nodes behaving like the honest spec
    -- Proofs that each of the honest nodes behave like the specification
    honest-nodes-≡-spec      : ∀ {p} → p ∈ honest-nodes → all-nodes p ≡ᴹ honest-node-spec
    -- The network machine
    network                  : Machine I (n ⨂ⁿ Network ⊗ NAdv)

  honest-nodes-blockchain : ∀ {p} → p ∈ honest-nodes → IsBlockchain (all-nodes p)
  honest-nodes-blockchain p-honest =
    ≡ᴹ-subst IsBlockchain (≡ᴹ-sym (honest-nodes-≡-spec p-honest)) spec-IsBlockchain

  -- Combination of all the nodes together
  nodes : Machine (n ⨂ⁿ Network) (⨂ IOF ⊗ ⨂ AdvF)
  nodes = ⨂ᴷ all-nodes

  Environment : Channel → Type₁
  Environment A = Machine (⨂ IOF ⊗ (NAdv ⊗ ⨂ AdvF)) A

  -- Composition of the nodes and the network
  protocol : ∀ {A} → Environment A → Machine I A
  protocol E = E CategoricalCrypto.∘ (nodes ∘ᴷ network)

  query : (bci : BlockChainInfo)
          {p : Fin n} {A : Channel}
          (E : Environment A)
          → Machine.State (protocol E)
          → p ∈ honest-nodes
          → bciQueryType bci
  query bci {p} _ (((_ , s , tt) , tt) , _) honest-p = proj₁ (queryCompute bci (⨂ᴷ-sub-state p s))
    where
      open IsBlockchain (honest-nodes-blockchain honest-p)
      open IsConstrained isConstrained

  getChain = query Chain

  safeState : {A : Channel} → ℕ → (E : Environment A) → Machine.State (protocol E) → Type
  safeState k E S =
    {p p'       : Fin n}
    (honest-p   : p  ∈ honest-nodes)
    (honest-p'  : p' ∈ honest-nodes)
    → prune k (getChain E S honest-p) ≼ getChain E S honest-p'

  safety : ℕ → Type₁
  safety k = ∀ {A} (E : Environment A) → Invariant (protocol E) (safeState k E)
