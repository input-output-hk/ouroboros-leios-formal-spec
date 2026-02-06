{-# OPTIONS --safe #-}

open import Leios.Prelude hiding (id; _⊗_)
open import Leios.Config
open import CategoricalCrypto hiding (id; _∘_)

module Leios.Safety (Block : Type) where

open import CategoricalCrypto.Machine.Constraints

-- | Type of things we can query from a honest node
data BlockChainInfo : Type where
  chain : BlockChainInfo
  slot  : BlockChainInfo

-- | Type for responses given a specific query
bciQueryType : BlockChainInfo → Type
bciQueryType chain = List Block
bciQueryType slot  = ℕ

record IsBlockchain {A B : Channel} (m : Machine A B) : Type₂ where
  field 
    isConstrained : IsConstrained m bciQueryType
    isDet         : IsDet isConstrained
    isPure        : IsPure isConstrained 

module _
  {A B : Channel}
  (m   : Machine A B) where
  
  open Machine m using () renaming (stepRel to _-⟦_/_⟧ᵐ⇀_)
  open Channel (A ⊗ B ᵀ)

  module m = Machine m

  data Trace : m.State → m.State → Type where
    []        : ∀ {s} → Trace s s
    _∷⟨_,_,_⟩ : ∀ {s s' s''} → Trace s s' → (i : inType) → (o : Maybe outType) → s' -⟦ i / o ⟧ᵐ⇀ s'' → Trace s s''

module _
  -- Number of involved nodes
  {n                       : ℕ}
  -- Communication channels involved in the network
  (IO Adv NAdv Network     : Channel)
  -- Machine describing the behavior of the honest nodes
  (honest-node-spec        : Machine Network (IO ⊗ Adv))
  -- All the nodes, including honest nodes and adversaries
  (all-nodes               : Fin n → Machine Network (IO ⊗ Adv))
  -- All the honest nodes
  (honest-nodes            : ℙ (Fin n)) -- Nodes behaving like the honest spec
  -- Proofs that each of the honest nodes behave like the specification
  (honest-nodes-≡-spec     : ∀ {p} → p ∈ honest-nodes → all-nodes p ≡ honest-node-spec)
  -- Proofs that each of the honest nodes is a blockchain (constrained, pure and
  -- deterministic with respect to bciQuerytype)
  (honest-nodes-blockchain : ∀ {p} → p ∈ honest-nodes → IsBlockchain (all-nodes p))
  -- The network machine
  (network                 : Machine I (n ⨂ⁿ Network ⊗ NAdv))
    where

  -- Combination of all the nodes together
  nodes : Machine (n ⨂ⁿ Network) (n ⨂ⁿ IO ⊗ n ⨂ⁿ Adv)
  nodes = ⨂ᴷ all-nodes

  -- Composition of the nodes and the network
  protocol : Machine I (n ⨂ⁿ IO ⊗ (NAdv ⊗ n ⨂ⁿ Adv))
  protocol = nodes ∘ᴷ network

  module protocol = Machine protocol

  query : (bci : BlockChainInfo)
          {p : Fin n}
          → protocol.State
          → p ∈ honest-nodes
          → bciQueryType bci
  query bci {p} ((_ , (s , tt)) , tt) honest-p = proj₁ (queryCompute bci (⨂ᴷ-sub-state p s))
    where
      open IsBlockchain (honest-nodes-blockchain honest-p)
      open IsDet isDet

  getChain = query chain
  getSlot = query slot

  safety : ℕ → ℕ → Type
  safety k Δ = (p p'       : Fin n)
               (honest-p   : p ∈ honest-nodes)
               (honest-p'  : p' ∈ honest-nodes)
               (init final : protocol.State)
               (tr         : Trace protocol init final)
               -- for all traces that reach `Δ` slots into the future
               → getSlot init honest-p + Δ ≤ getSlot final honest-p
               -- all honest nodes have `chain` as a prefix
               → prune k (getChain init honest-p) ≼ getChain final honest-p'

